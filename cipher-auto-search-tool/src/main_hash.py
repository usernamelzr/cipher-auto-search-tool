from node import *
from node_constraint import *
from hash import get_message_per_round_structure
from cipher_parser import get_node_parent_index_list
import SAT_util
import copy
import os
import subprocess

main_hash_cipher_name = ""
    
# 构造一轮的SAT模型
def execute_one_round(var_number, execute_structure, input_node, nodes_execute_his, with_cond, round_index=0):
    pre_round_nodes, nodes_per_round, post_round_nodes = nodes_execute_his
    nodes = dict()
    clauses = []
    # auxiliary_variables为字典，保存每个节点执行时声明的辅助变量（目前应该只有AddNode保存了进位变量）
    auxiliary_variables = dict()
    output_node = None
    execute_index_sequence = sorted(execute_structure)
    root_index = execute_index_sequence[0]
    # 轮函数结构的起始节点必须为RootNode
    if not isinstance(execute_structure[root_index], RootNode):
        raise_error("轮函数的首节点必须为ROOT节点!")
    # 本轮的根节点换成上一轮的末节点
    nodes[root_index] = input_node
    # 先声明轮中所有节点
    for index in execute_index_sequence[1:]:
        if isinstance(execute_structure[index], ParallelSBoxNode):
            # 共用同一个子句列表
            nodes[index] = copy.copy(execute_structure[index])
        else:
            nodes[index] = copy.deepcopy(execute_structure[index])
    # 按照编号升序执行轮占每个节点
    for index in execute_index_sequence[1:]:
        node = nodes[index]
        if isinstance(node, SplitNode):
            var_number, _, _ = node.hash_execute(var_number, nodes[node.parent_index], with_cond)
        elif isinstance(node, MergeNode):
            parent_list = [nodes[i] for i in node.parent_index_list]
            var_number, _, _ = node.hash_execute(var_number, parent_list, with_cond)
        elif isinstance(node, XORNode):
            parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, RotationNode):
            var_number, _, _ = node.hash_execute(var_number, nodes[node.parent_index], round_index, with_cond)
        elif isinstance(node, ShiftNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, nodes[node.parent_index], round_index, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, BranchNode):
            parent = nodes[node.parent_index]
            var_number, _, _ = node.hash_execute(var_number, parent, with_cond)
        elif isinstance(node, ParallelSBoxNode):
            parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
            output_list = [nodes[output_index] for output_index in node.output_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, output_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, AddNode):
            parent1 = nodes[node.parent_index1]
            parent2 = nodes[node.parent_index2]
            var_number, tmp_clauses, auxiliary_variables[index] = node.hash_execute(var_number, parent1, parent2, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, EqualNode):
            var_number, _, _ = node.hash_execute(var_number, nodes[node.parent_index], with_cond)
        elif isinstance(node, ConstantNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, round_index, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, EndNode):
            var_number, _, _ = node.hash_execute(var_number, nodes[node.parent_index], with_cond)
            output_node = node
            break
        elif isinstance(node, MessageNode):
            var_number, _, _ = node.hash_execute(var_number, with_cond)
        elif isinstance(node, SBoxNode):
            parent = nodes[node.parent_index]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, PNode):
            parent = nodes[node.parent_index]
            var_number, _, _ = node.hash_execute(var_number, parent, with_cond)
        elif isinstance(node, FNode):
            parent_list = [nodes[i] for i in node.parent_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, ImportNode):
            if node.round_index >= 0:
                tnodes = nodes_per_round[node.round_index]
                if node.index_in_round not in tnodes:
                    raise_error("IMPORT引用了轮函数中不存在的节点! IMPORT节点编号{}, 引用了第{}轮的节点{}!".format(node.index, node.round_index, node.index_in_round))
                var_number, _, _ = node.hash_execute(var_number, tnodes[node.index_in_round], with_cond)
            elif node.round_index == -2:
                if node.index_in_round not in pre_round_nodes:
                    raise_error("IMPORT引用了PREROUND部分中不存在的节点! IMPORT节点编号{}, 引用了PREROUND的节点{}!".format(node.index, node.index_in_round))
                var_number, _, _ = node.hash_execute(var_number, pre_round_nodes[node.index_in_round], with_cond)
            else:
                assert node.round_index < -2
                target_round_index = round_index + 2 + node.round_index
                if target_round_index < 0:
                    raise_error("第{}轮的IMPORT节点{}引用了第{}轮的节点!".format(round_index, node.index, target_round_index))
                tnodes = nodes_per_round[target_round_index]
                if node.index_in_round not in tnodes:
                    raise_error("IMPORT引用了轮函数中不存在的节点! IMPORT节点编号{}, 引用了第{}轮的节点{}!".format(node.index, target_round_index, node.index_in_round))
                var_number, _, _ = node.hash_execute(var_number, tnodes[node.index_in_round], with_cond)
        else:
            raise_error("Hash碰撞分析中不支持的节点类型: {}!".format(node.node_name))
    # 轮函数中必须存在末节点
    if output_node is None:
        raise_error("轮函数中找不到END节点")
    return var_number, output_node, nodes, clauses, auxiliary_variables

# 将消息扩展结构执行一遍，返回变量编号起点var_number以及约束
def execute_message_expand_info(var_number, message_expand_tuple, message_size_per_round, with_cond):
    nodes = dict()
    clauses = []
    message_nodes = message_expand_tuple[0]
    message_indexes = message_expand_tuple[1]
    # 特判：没有消息扩展结构就不用执行
    if not message_indexes:
        return var_number, clauses, nodes, []
    # 首先得到必须要算的节点编号
    necessary_node_indexes = dict()
    necessary_message_indexes = []
    index = 0
    round_number = len(message_size_per_round) - 2
    for i in ([-2] + [i for i in range(round_number)]):
        message_num = len(message_size_per_round[i])
        necessary_message_indexes += message_indexes[index:index+message_num]
        index += message_num
    necessary_message_indexes += message_indexes[-1-len(message_size_per_round[-1]):-1]
    message_index_max = 0
    for message_index in necessary_message_indexes:
        if message_index > message_index_max:
            message_index_max = message_index
        necessary_node_indexes[message_index] = 1
    for i in range(message_index_max, -1, -1):
        if i not in necessary_node_indexes:
            continue
        for parent_index in get_node_parent_index_list(message_nodes[i]):
            necessary_node_indexes[parent_index] = 1
    execute_index_sequence = sorted(necessary_node_indexes)
    # 先声明计算结构中所有节点
    for index in execute_index_sequence:
        if isinstance(message_nodes[index], ParallelSBoxNode):
            # 共用一个字句列表
            nodes[index] = copy.copy(message_nodes[index])
        else:
            nodes[index] = copy.deepcopy(message_nodes[index])
    # 按照编号升序执行
    for index in execute_index_sequence:
        node = nodes[index]
        if isinstance(node, SplitNode) or isinstance(node, EqualNode) or isinstance(node, SBoxNode) or isinstance(node, PNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, nodes[node.parent_index], with_cond)
            clauses += tmp_clauses
        elif isinstance(node, XORNode) or isinstance(node, MergeNode) or isinstance(node, FNode):
            parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, RotationNode) or isinstance(node, ShiftNode) or isinstance(node, BranchNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, nodes[node.parent_index], 0, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, AddNode):
            parent1 = nodes[node.parent_index1]
            parent2 = nodes[node.parent_index2]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent1, parent2, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, ConstantNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, 0, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, ParallelSBoxNode):
            parent_list = [nodes[parent_index] for parent_index in node.parent_index_list]
            output_list = [nodes[output_index] for output_index in node.output_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, output_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, MessageNode):
            var_number, _, _ = node.hash_execute(var_number, with_cond)
        else:
            raise_error("正在构建模差分SAT模型, 消息扩展结构中存在非法节点, 节点类型{}!".format(node.node_name))
    return var_number, clauses, nodes, necessary_message_indexes
        
def apply_node_constraints(round_number, var_number, pre_round_nodes, nodes_per_round, post_round_nodes, constraint_nodes, constraints, with_cond):
    execute_index_sequence = sorted(constraint_nodes)
    clauses = []
    # 首先将约束部分节点全部执行一遍
    for index in execute_index_sequence:
        node = constraint_nodes[index]
        if isinstance(node, ImportNode):
            # 约束部分通过ImportNode引入轮函数中的节点
            if node.round_index == -2:
                # 轮前节点
                if node.index_in_round not in pre_round_nodes:
                    raise_error("约束部分编号为{}的IMPORT节点中, 在轮前结构中找不到编号为{}的节点!".format(index, node.index_in_round))
                target_node = pre_round_nodes[node.index_in_round]
            elif node.round_index == -1:
                # 轮后节点
                if node.index_in_round not in post_round_nodes:
                    raise_error("约束部分编号为{}的IMPORT节点中, 在轮后结构中找不到编号为{}的节点!".format(index, node.index_in_round))
                target_node = post_round_nodes[node.index_in_round]
            else:
                # 轮函数内节点
                if node.round_index < 0 or node.round_index >= round_number:
                    raise_error("约束部分编号为{}的IMPORT节点中, 引用轮次{}错误!".format(index, node.round_index))
                if node.index_in_round not in nodes_per_round[node.round_index]:
                    raise_error("约束部分编号为{}的IMPORT节点中, 在轮函数第{}轮中找不到编号为{}的节点!".format(index, node.round_index, node.index_in_round))
                target_node = nodes_per_round[node.round_index][node.index_in_round]
            var_number, _, _ = node.hash_execute(var_number, target_node, with_cond)
        elif isinstance(node, SplitNode):
            var_number, _, _ = node.hash_execute(var_number, constraint_nodes[node.parent_index], with_cond)
        elif isinstance(node, MergeNode):
            parent_list = [constraint_nodes[i] for i in node.parent_index_list]
            var_number, _, _ = node.hash_execute(var_number, parent_list, with_cond)
        elif isinstance(node, XORNode):
            parent_list = [constraint_nodes[parent_index] for parent_index in node.parent_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, RotationNode):
            var_number, _, _ = node.hash_execute(var_number, constraint_nodes[node.parent_index], 0, with_cond)
        elif isinstance(node, ShiftNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, constraint_nodes[node.parent_index], 0, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, BranchNode):
            parent = constraint_nodes[node.parent_index]
            var_number, _, _ = node.hash_execute(var_number, parent, with_cond)
        elif isinstance(node, ParallelSBoxNode):
            parent_list = [constraint_nodes[parent_index] for parent_index in node.parent_index_list]
            output_list = [constraint_nodes[output_index] for output_index in node.output_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, output_list, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, AddNode):
            parent1 = constraint_nodes[node.parent_index1]
            parent2 = constraint_nodes[node.parent_index2]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent1, parent2, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, EqualNode):
            var_number, _, _ = node.hash_execute(var_number, constraint_nodes[node.parent_index], with_cond)
        elif isinstance(node, ConstantNode):
            var_number, tmp_clauses, _ = node.hash_execute(var_number, 0, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, SBoxNode):
            parent = constraint_nodes[node.parent_index]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent, with_cond)
            clauses += tmp_clauses
        elif isinstance(node, PNode):
            parent = constraint_nodes[node.parent_index]
            var_number, _, _ = node.hash_execute(var_number, parent, with_cond)
        elif isinstance(node, FNode):
            parent_list = [constraint_nodes[i] for i in node.parent_index_list]
            var_number, tmp_clauses, _ = node.hash_execute(var_number, parent_list, with_cond)
            clauses += tmp_clauses
        else:
            raise_error("约束部分不支持的节点类型: {}!".format(node.node_name))
    # 为节点添加约束
    for constraint in constraints:
        if isinstance(constraint, ConstantConstraint) or isinstance(constraint, UnequalConstantConstraint):
            target_node = constraint_nodes[constraint.target_node_index]
            var_number, tmp_clauses, _ =  constraint.apply(var_number, target_node)
            clauses += tmp_clauses
        elif isinstance(constraint, EqualConstraint):
            target_node_1 = constraint_nodes[constraint.target_node_index_1]
            target_node_2 = constraint_nodes[constraint.target_node_index_2]
            var_number, tmp_clauses, _ = constraint.apply(var_number, target_node_1, target_node_2)
            clauses += tmp_clauses
        elif isinstance(constraint, UnequalConstraint):
            target_node_1 = constraint_nodes[constraint.target_node_index_1]
            target_node_2 = constraint_nodes[constraint.target_node_index_2]
            var_number, tmp_clauses, auxiliary_variables = constraint.apply(var_number, target_node_1, target_node_2)
            clauses += tmp_clauses
        elif isinstance(constraint, MdiffConstraint):
            target_node = constraint_nodes[constraint.target_node_index]
            var_number, tmp_clauses, _ = constraint.apply(var_number, target_node)
            clauses += tmp_clauses
        elif isinstance(constraint, ConditionConstraint):
            target_node = constraint_nodes[constraint.target_node_index]
            fore_node = constraint_nodes[constraint.fore_node_index]
            var_number, tmp_clauses, _ = constraint.apply(var_number, target_node, fore_node)
            clauses += tmp_clauses
        elif isinstance(constraint, ConditionSumConstraint):
            target_nodes = [constraint_nodes[i] for i in constraint.target_node_indexes]
            var_number, tmp_clauses, _ = constraint.apply(var_number, target_nodes)
            clauses += tmp_clauses
        elif isinstance(constraint, DiffSumConstraint):
            target_nodes = [constraint_nodes[i] for i in constraint.target_node_indexes]
            var_number, tmp_clauses, _ = constraint.apply(var_number, target_nodes)
            clauses += tmp_clauses
    return var_number, clauses

def combine_message_and_body(nodes_execute_his, message_expand_nodes, message_indexes):
    clauses = []
    pre_round_nodes, nodes_per_round, post_round_nodes = nodes_execute_his
    combined_num = 0
    if pre_round_nodes:
        for index in sorted(pre_round_nodes):
            if isinstance(pre_round_nodes[index], MessageNode):
                node1 = pre_round_nodes[index]
                node2 = message_expand_nodes[message_indexes[combined_num]]
                combined_num += 1
                if node1.size != node2.size:
                    raise_error("正在构建模差分SAT模型, 轮前消息节点长度({})与消息扩展中长度({})不一致!".format(node1.size, node2.size))
                tmp_constraint = EqualConstraint(0, 0, [i for i in range(node1.size)], "diff")
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
                tmp_constraint.category = "real"
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
    for nodes in nodes_per_round:
        for index in sorted(nodes):
            if isinstance(nodes[index], MessageNode):
                node1 = nodes[index]
                node2 = message_expand_nodes[message_indexes[combined_num]]
                combined_num += 1
                if node1.size != node2.size:
                    raise_error("正在构建模差分SAT模型, 轮函数消息节点长度({})与消息扩展中长度({})不一致!".format(node1.size, node2.size))
                tmp_constraint = EqualConstraint(0, 0, [i for i in range(node1.size)], "diff")
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
                tmp_constraint.category = "real"
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
    if post_round_nodes:
        for index in sorted(post_round_nodes):
            if isinstance(post_round_nodes[index], MessageNode):
                node1 = post_round_nodes[index]
                node2 = message_expand_nodes[message_indexes[combined_num]]
                combined_num += 1
                if node1.size != node2.size:
                    raise_error("正在构建模差分SAT模型, 轮后消息节点长度({})与消息扩展中长度({})不一致!".format(node1.size, node2.size))
                tmp_constraint = EqualConstraint(0, 0, [i for i in range(node1.size)], "diff")
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
                tmp_constraint.category = "real"
                _, tmp_clauses, _ = tmp_constraint.apply(0, node1, node2)
                clauses += tmp_clauses
    return clauses

def execute_SAT(cipher, round_number, constraint_nodes, constraints, message_expand_info, with_cond):
    global main_hash_cipher_name
    pre_round, post_round, cipher_bodys, cipher_body_loop_num = cipher[0], cipher[1], cipher[2][0], cipher[2][1]
    # 将所有循环体串联起来
    loop_num = len(cipher_body_loop_num)
    round_structure_list = []
    for i in range(loop_num):
        for _ in range(cipher_body_loop_num[i]):
            round_structure_list.append(cipher_bodys[i])
    round_structure_list = round_structure_list[:round_number]
    pre_round_nodes = dict()
    post_round_nodes = dict()
    nodes_per_round = []
    nodes_execute_his = (pre_round_nodes, nodes_per_round, post_round_nodes)
    auxiliary_variables_per_round = []
    round_nodes = []
    # 编号必须从1开始
    var_number = 1
    clauses = []
    # 执行轮前结构
    if pre_round:
        execute_index_sequence = sorted(pre_round)
        start_node = copy.deepcopy(pre_round[execute_index_sequence[0]])
        var_number, _, _ = start_node.hash_execute(var_number, with_cond)
        round_nodes.append(start_node)
        var_number, start_node, pre_round_nodes, tmp_clauses, auxiliary_variables = execute_one_round(var_number, pre_round, start_node, nodes_execute_his, with_cond)
        clauses += tmp_clauses
        auxiliary_variables_per_round.append(auxiliary_variables)
    else:
        execute_index_sequence = sorted(round_structure_list[0])
        start_node = copy.deepcopy(round_structure_list[0][execute_index_sequence[0]])
        var_number, _, _ = start_node.hash_execute(var_number, with_cond)
    # 执行轮函数中串联后的循环体
    nodes_execute_his = (pre_round_nodes, nodes_per_round, post_round_nodes)
    round_nodes.append(start_node)
    for r in range(round_number):
        var_number, output_node, nodes, tmp_clauses, auxiliary_variables = execute_one_round(var_number, round_structure_list[r], round_nodes[-1], nodes_execute_his, with_cond, r)
        round_nodes.append(output_node)
        nodes_per_round.append(nodes)
        clauses += tmp_clauses
        auxiliary_variables_per_round.append(auxiliary_variables)
    # 执行轮后结构
    if post_round:
        var_number, output_node, post_round_nodes, tmp_clauses, auxiliary_variables = execute_one_round(var_number, post_round, round_nodes[-1], nodes_execute_his, with_cond)
        round_nodes.append(output_node)
        clauses += tmp_clauses
        auxiliary_variables_per_round.append(auxiliary_variables)
    # 执行消息扩展结构
    message_indexes = message_expand_info[1]
    message_size_per_round = get_message_per_round_structure(cipher, round_number)[0][1]
    var_number, tmp_clauses, message_expand_nodes, necessary_message_indexes = execute_message_expand_info(var_number, message_expand_info, message_size_per_round, with_cond)
    clauses += tmp_clauses
    if message_indexes:
        # 需要将消息扩展结构与轮函数接起来
        tmp_clauses = combine_message_and_body(nodes_execute_his, message_expand_nodes, necessary_message_indexes)
        clauses += tmp_clauses
    # 为节点添加约束
    var_number, tmp_clauses = apply_node_constraints(round_number, var_number, pre_round_nodes, nodes_per_round, post_round_nodes, constraint_nodes, constraints, with_cond)
    clauses += tmp_clauses
    # 构造SAT求解器输入文件
    var_number -= 1
    SAT_input_path = SAT_util.SAT_tmp_folder + f"SAT_input_{main_hash_cipher_name}_hash_{round_number}.cnf"
    SAT_output_path = SAT_util.SAT_tmp_folder + f"SAT_solution_{main_hash_cipher_name}_hash_{round_number}.out"
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
        nodes_per_round_solution = []
        round_nodes_solution = []
        pre_round_solution = dict()
        post_round_solution = dict()
        for round_node in round_nodes:
            round_node_solution = [var_solution[i] for i in round_node.variables]
            if with_cond:
                assert len(round_node.variables) == 2 * len(round_node.cond_vars)
                round_node_solution += [var_solution[i] for i in round_node.cond_vars]
            round_nodes_solution.append(round_node_solution)
        for nodes in nodes_per_round:
            nodes_solution = dict()
            for key, value in nodes.items():
                nodes_solution[key] = [var_solution[i] for i in value.variables]
                if with_cond:
                    assert len(value.variables) == 2 * len(value.cond_vars)
                    nodes_solution[key] += [var_solution[i] for i in value.cond_vars]
            nodes_per_round_solution.append(nodes_solution)
        for key, value in pre_round_nodes.items():
            pre_round_solution[key] = [var_solution[i] for i in value.variables]
            if with_cond:
                assert len(value.variables) == 2 * len(value.cond_vars)
                pre_round_solution[key] += [var_solution[i] for i in value.cond_vars]
        for key, value in post_round_nodes.items():
            post_round_solution[key] = [var_solution[i] for i in value.variables]
            if with_cond:
                assert len(value.variables) == 2 * len(value.cond_vars)
                post_round_solution[key] += [var_solution[i] for i in value.cond_vars]
        return True, round_nodes_solution, nodes_per_round_solution, pre_round_solution, post_round_solution
    else:
        return False, None, None, None, None
    
def do_cryptanalysis(cipher, cipher_name, cipher_block_size, round_number, constraint_info, message_expand_info):
    global main_hash_cipher_name
    main_hash_cipher_name = cipher_name
    constraint_nodes, constraints, with_cond = constraint_info
    save_path = SAT_util.search_res_path(cipher_name, "diff_real")
    save_path = open(save_path, "w", encoding="utf-8")
    save_path.write("----------------------------------" + cipher_name + "密码的哈希碰撞搜索结果----------------------------------\n")
    pre_round, post_round = cipher[0], cipher[1]
    is_SAT, round_nodes_solution, nodes_per_round_solution, pre_round_solution, post_round_solution = execute_SAT(cipher, round_number, constraint_nodes, constraints, message_expand_info, with_cond)
    if is_SAT:
        print("找到一条{}轮路线!".format(round_number))
        save_path.write("找到一条{}轮路线!\n".format(round_number))
        save_path.write("\n路线每轮输入输出状态:\n")
        format_string = "| {:^11} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, len("Difference Value"))) + "} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, len("State1 Value"))) + "} |\n"
        format_string_value = "{:#0" + str((cipher_block_size + 3) // 4 + 2) + "x}"
        save_path.write(format_string.format("Round Index", "Difference Value", "State1 Value"))
        index = 0
        if pre_round:
            # 有轮前结构
            save_path.write(format_string.format("Pre Round", format_string_value.format(bits_to_int(round_nodes_solution[index][:cipher_block_size])), format_string_value.format(bits_to_int(round_nodes_solution[index][cipher_block_size:2*cipher_block_size]))))
            index += 1
        for i in range(round_number + 1):
            save_path.write(format_string.format(i, format_string_value.format(bits_to_int(round_nodes_solution[index][:cipher_block_size])), format_string_value.format(bits_to_int(round_nodes_solution[index][cipher_block_size:2*cipher_block_size]))))
            index += 1
        if post_round:
            # 有轮后结构
            save_path.write(format_string.format("Post Round", format_string_value.format(bits_to_int(round_nodes_solution[index][:cipher_block_size])), format_string_value.format(bits_to_int(round_nodes_solution[index][cipher_block_size:2*cipher_block_size]))))
            index += 1

        save_path.write("\n每轮各节点详细信息:\n")
        format_string = "| {:^10} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, len("Difference Value"))) + "} | {:^" + str(max((cipher_block_size + 3) // 4 + 2, len("State1 Value"))) + "} |\n"
        if pre_round_solution:
            save_path.write("\n----------------------------------轮函数前----------------------------------\n")
            # 输出表头
            save_path.write(format_string.format("Node Index", "Difference Value", "State1 Value"))
            index_sequence = sorted(pre_round_solution)
            for i in index_sequence:
                state_size = (len(pre_round_solution[i]) // 3) if with_cond else (len(pre_round_solution[i]) // 2)
                format_string_value = "{:#0" + str((state_size + 3) // 4 + 2) + "x}"
                save_path.write(format_string.format(i, format_string_value.format(bits_to_int(pre_round_solution[i][:state_size])), format_string_value.format(bits_to_int(pre_round_solution[i][state_size:2*state_size]))))
        for i in range(round_number):
            save_path.write("\n----------------------------------第{}轮----------------------------------\n".format(i))
            # 输出表头
            save_path.write(format_string.format("Node Index", "Difference Value", "State1 Value"))
            nodes_solution = nodes_per_round_solution[i]
            index_sequence = sorted(nodes_solution)
            for j in index_sequence:
                state_size = (len(nodes_solution[j]) // 3) if with_cond else (len(nodes_solution[j]) // 2)
                format_string_value = "{:#0" + str((state_size + 3) // 4 + 2) + "x}"
                save_path.write(format_string.format(j, format_string_value.format(bits_to_int(nodes_solution[j][:state_size])), format_string_value.format(bits_to_int(nodes_solution[j][state_size:2*state_size]))))
        if post_round_solution:
            save_path.write("\n----------------------------------轮函数后----------------------------------\n")
            # 输出表头
            save_path.write(format_string.format("Node Index", "Difference Value", "State1 Value"))
            index_sequence = sorted(post_round_solution)
            for i in index_sequence:
                state_size = (len(post_round_solution[i]) // 3) if with_cond else (len(post_round_solution[i]) // 2)
                format_string_value = "{:#0" + str((state_size + 3) // 4 + 2) + "x}"
                save_path.write(format_string.format(i, format_string_value.format(bits_to_int(post_round_solution[i][:state_size])), format_string_value.format(bits_to_int(post_round_solution[i][state_size:2*state_size]))))
    else:
        print("不存在满足条件的{}轮路线!".format(round_number))
        save_path.write("不存在满足条件的{}轮路线!\n".format(round_number))
    save_path.close()