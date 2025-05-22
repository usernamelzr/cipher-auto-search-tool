from node import *
from bounding_condition import *
import SAT_util
import copy
import os
import subprocess
from node_constraint import *
from error_handler import raise_error

main_cipher_name = ""

# 执行一个操作节点
# 返回 var_number, clauses, counter_variables
def execute_operation_node(node, nodes, var_number, is_search_diff, round_index):
    if isinstance(node, SplitNode):
        return node.execute(var_number, nodes[node.parent_index])
    if isinstance(node, MergeNode):
        parent_list = [nodes[i] for i in node.parent_index_list]
        return node.execute(var_number, parent_list)
    if isinstance(node, XORNode):
        parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
        return node.execute(var_number, parent_list, is_search_diff)
    if isinstance(node, RotationNode):
        return node.execute(var_number, nodes[node.parent_index], round_index)
    if isinstance(node, ShiftNode):
        return node.execute(var_number, nodes[node.parent_index], is_search_diff, round_index)
    if isinstance(node, BranchNode):
        parent = nodes[node.parent_index]
        out_list = [nodes[out_index] for out_index in node.out_index_list]
        return node.execute(var_number, parent, out_list, is_search_diff)
    if isinstance(node, FNode):
        parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
        return node.execute(var_number, parent_list, is_search_diff)
    if isinstance(node, ParallelSBoxNode):
        parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
        output_list = [nodes[output_index] for output_index in node.output_index_list]
        return node.execute(var_number, parent_list, output_list, is_search_diff)
    if isinstance(node, AddNode):
        parent1 = nodes[node.parent_index1]
        parent2 = nodes[node.parent_index2]
        return node.execute(var_number, parent1, parent2, is_search_diff)
    if isinstance(node, SubKeyNode) or isinstance(node, MessageNode):
        return node.execute(var_number, is_search_diff)
    if isinstance(node, ConstantNode):
        return node.execute(var_number, round_index, is_search_diff)
    if isinstance(node, EndNode):
        return node.execute(var_number, nodes[node.parent_index])
    if isinstance(node, SBoxNode):
        parent = nodes[node.parent_index]
        return node.execute(var_number, parent, is_search_diff)
    if isinstance(node, PNode) or isinstance(node, EqualNode):
        parent = nodes[node.parent_index]
        return node.execute(var_number, parent)
    raise_error("差分分析、线性分析、以及差分线性分析中不支持的节点类型: {}!".format(node.node_name))

# 构造一轮的SAT模型
def execute_one_round(var_number, execute_structure, input_node, execute_index_sequence, is_search_diff, round_index):
    nodes = dict()
    clauses = []
    counter_variables = []
    output_node = None
    root_index = execute_index_sequence[0]
    # 轮函数结构的起始节点必须为RootNode
    if not isinstance(execute_structure[root_index], RootNode):
        raise_error("轮函数的首节点必须为ROOT节点!")
    # 本轮的根节点换成上一轮的末节点
    nodes[root_index] = input_node
    for index in execute_index_sequence[1:]:
        if isinstance(execute_structure[index], ParallelSBoxNode):
            # 共用同一个子句列表
            nodes[index] = copy.copy(execute_structure[index])
        else:
            nodes[index] = copy.deepcopy(execute_structure[index])
    for index in execute_index_sequence[1:]:
        node = nodes[index]
        var_number, tmp_clauses, tmp_counter_variables = execute_operation_node(node, nodes, var_number, is_search_diff, round_index)
        clauses += tmp_clauses
        counter_variables += tmp_counter_variables
        if isinstance(node, EndNode):
            output_node = node
            break
    # 轮函数中必须存在末节点
    if output_node is None:
        raise_error("轮函数中找不到END节点")
    return var_number, output_node, nodes, clauses, counter_variables

# 执行约束部分
# 返回: var_number, clauses, head_constraint_flag, tail_constriant_flag
def apply_node_constraints(var_number, nodes_per_round, constraint_nodes, constraints, is_search_diff):
    execute_index_sequence = sorted(constraint_nodes)
    clauses = []
    head_constraint_flag = False
    tail_constraint_flag = False
    # 首先将约束部分节点全部执行一遍
    for index in execute_index_sequence:
        node = constraint_nodes[index]
        if isinstance(node, HeadImportNode):
            # 约束部分通过HEAD_IMPORT引入首轮中节点
            target_node = nodes_per_round[0][node.index_in_round]
            var_number, _, _ = node.execute(var_number, target_node)
            head_constraint_flag = True
        elif isinstance(node, TailImportNode):
            # 约束部分通过TAIL_IMPORT引入尾轮中节点
            target_node = nodes_per_round[-1][node.index_in_round]
            var_number, _, _ = node.execute(var_number, target_node)
            tail_constraint_flag = True
        else:
            var_number, tmp_clauses, tmp_counter_variables = execute_operation_node(node, constraint_nodes, var_number, is_search_diff, 0)
            if tmp_counter_variables:
                raise_error("解析到{}节点，差分、线性搜索的约束部分计算中不能涉及概率操作!".format(node.node_name))
            clauses += tmp_clauses
    # 为节点添加约束
    for constraint in constraints:
        if isinstance(constraint, ConstantConstraint):
            target_node = constraint_nodes[constraint.target_node_index]
            var_number, tmp_clauses, _ = constraint.apply_d_l(var_number, target_node, is_search_diff)
            clauses += tmp_clauses
        else:
            raise_error("差分、线性搜索的约束部分解析到不支持的约束类型: {}!".format(constraint.constraint_name))
    return var_number, clauses, head_constraint_flag, tail_constraint_flag

def execute_SAT(cipher_body, round_number, counter_upper_bound, his_counter_upper_bound, constraint_nodes, constraints, is_search_diff=True):
    global main_cipher_name
    execute_index_sequence = sorted(cipher_body)
    clauses = []
    counter_variables_per_round = []
    counter_variables = []
    # 编号必须从1（非零）开始
    var_number = 1
    nodes_per_round = []
    round_nodes = []
    root_node = copy.deepcopy(cipher_body[execute_index_sequence[0]])
    # 执行轮函数迭代的起始节点
    var_number, _, _ = root_node.execute(var_number)
    round_nodes.append(root_node)
    # 添加非平凡解限制
    clauses.append(root_node.variables[:])
    for r in range(round_number):
        var_number, output_node, nodes, tmp_clauses, round_counter_variables = execute_one_round(var_number, cipher_body, round_nodes[-1], execute_index_sequence, is_search_diff, r)
        clauses += tmp_clauses
        round_nodes.append(output_node)
        nodes_per_round.append(nodes)
        counter_variables_per_round.append(round_counter_variables)
        counter_variables += round_counter_variables
    # 执行约束部分
    var_number, tmp_clauses, head_constraint_flag, tail_constraint_flag = apply_node_constraints(var_number, nodes_per_round, constraint_nodes, constraints, is_search_diff)
    clauses += tmp_clauses
    var_number, tmp_clauses, s = sequential_encoding(var_number, counter_variables, counter_upper_bound)
    clauses += tmp_clauses
    clauses += add_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound, not head_constraint_flag, not tail_constraint_flag)
    # 构造SAT求解器输入文件
    var_number -= 1
    SAT_input_path = SAT_util.SAT_tmp_folder + "SAT_input_{}_{}_{}_{}.cnf".format(main_cipher_name, "diff" if is_search_diff else "linear", round_number, counter_upper_bound)
    SAT_output_path = SAT_util.SAT_tmp_folder + "SAT_solution_{}_{}_{}_{}.out".format(main_cipher_name, "diff" if is_search_diff else "linear", round_number, counter_upper_bound)
    SAT_util.construct_dimacs_input(SAT_input_path, clauses, var_number)
    cmd_str = SAT_util.CaDiCaL_cmd + " " +  SAT_input_path + " > " + SAT_output_path
    res = subprocess.call(cmd_str, env=SAT_util.env_para, shell=True)
    # 判断是否SAT
    var_solution = SAT_util.get_var_solution(SAT_output_path)
    # 删除输入输出文件
    order = SAT_util.del_cmd + f" {SAT_input_path}"
    os.system(order)
    order = SAT_util.del_cmd + f" {SAT_output_path}"
    os.system(order)
    if var_solution:
        round_nodes_solution = []
        for round_node in round_nodes:
            round_node_solution = [var_solution[i] for i in round_node.variables]
            round_nodes_solution.append(round_node_solution)
        counter_variables_solution = []
        for cv in counter_variables_per_round:
            counter_variables_solution.append([var_solution[i] for i in cv])
        return True, round_nodes_solution, counter_variables_solution
    else:
        return False, [], []

# 差分或线性分析忽略轮函数前（.PREROUND）和轮函数后（.POSTROUND）结构，只对核心的轮函数进行搜索
# 差分或线性分析采用迭代搜索，只能对轮函数中的一个循环体进行搜索
# 选择第search_loop_index个循环体，按照算法总轮数进行搜索
def do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number, constraint_info, is_search_diff, whether_consider_pr=True):
    global main_cipher_name
    main_cipher_name = cipher_name
    constraint_nodes, constraints, with_cond = constraint_info
    round_number = 1
    counter_upper_bound = 0
    # 要搜索轮函数第search_loop_index个循环体
    cipher_body = cipher[2][0][search_loop_index]
    his_counter_upper_bound = [0]
    save_path = SAT_util.search_res_path(cipher_name, "diff" if is_search_diff else "linear", whether_consider_pr)
    save_path = open(save_path, "w", buffering=1, encoding="utf-8")
    save_path.write("----------------------------------" + cipher_name + "密码的" + ("差分分析结果" if is_search_diff else "线性分析结果") + "----------------------------------\n")
    while round_number <= cipher_round_number and counter_upper_bound < cipher_block_size:
        # print(f"[Debug] trying: round number = {round_number}, counter upper bound = {counter_upper_bound}.")
        is_SAT, round_nodes_solution, counter_variables_solution = execute_SAT(cipher_body, round_number, counter_upper_bound, his_counter_upper_bound, constraint_nodes, constraints, is_search_diff)
        if is_SAT:
            if whether_consider_pr:
                print("\n分析轮数: {}, 最优路线{}: 2^-{}".format(round_number, "概率" if is_search_diff else "相关性", counter_upper_bound))
            else:
                print("\n分析轮数: {}, 最优路线{}: {}个".format(round_number, "活跃S盒数量", counter_upper_bound))
            # 将结果保存至文件
            if whether_consider_pr:
                save_path.write("\n找到最好的{}轮路线, {}为2^-{}:\n".format(round_number, "概率" if is_search_diff else "相关性", counter_upper_bound))
            else:
                save_path.write("\n找到最好的{}轮路线, 活跃S盒数量为{}个\n".format(round_number, counter_upper_bound))
            counter_variables_solution = [[0]] + counter_variables_solution
            # 输出表头
            if whether_consider_pr:
                format_string = "| {:^11} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, 18)) + "} | {:^6} |\n"
            else:
                format_string = "| {:^11} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, 18)) + "} | {:^15} |\n"
            if whether_consider_pr:
                save_path.write(format_string.format("Round Index", "Differential Value", "Pr" if is_search_diff else "Cor"))
            else:
                save_path.write(format_string.format("Round Index", "Differential Value", "#Active S-Box"))
            # 输出内容
            if whether_consider_pr:
                format_string = "| {:^11} | {:#0" + str(max((cipher_block_size + 3) // 4 + 2, 18)) + "x} | {:^6} |\n"
            else:
                format_string = "| {:^11} | {:#0" + str(max((cipher_block_size + 3) // 4 + 2, 18)) + "x} | {:^15} |\n"
            for i in range(round_number + 1):
                counter_sum = 0
                for j in counter_variables_solution[i]:
                    counter_sum += j
                save_path.write(format_string.format(i, bits_to_int(round_nodes_solution[i], False), f"2^-{counter_sum}" if whether_consider_pr else counter_sum))
            round_number += 1
            his_counter_upper_bound.append(counter_upper_bound)
        else:
            counter_upper_bound += 1
    save_path.close()