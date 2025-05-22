from node import *
from bounding_condition import *
from node_constraint import *
from util import bits_to_int, int_to_bits
from main_d_l import execute_one_round
import SAT_util
from encryption import encrypt_n_rounds
import copy
import os
import subprocess

main_dl_cipher_name = ""

# 目前只测1比特差分以及1比特线性掩码
def find_good_diff_liear_via_experiment(cipher_block_size, round_structure, n=2**20, cor_t=5):
    # round_number从1轮开始尝试，直到搜不出相关性大于等于2^-5的特征停止
    # 目前最多搜cipher_block_size条路线
    # 保证实验数据足够多
    assert math.log2(n) / 2 - 2 >= cor_t
    best_short_diff_linear = [(0, 0, 0)]
    max_diff_linear_num = cipher_block_size
    round_number = 1
    while True:
        best_cor = cor_t + 1
        tmp_collector = []
        plaintext_bits1, ciphertext_bits1, round_keys_list = encrypt_n_rounds(round_structure, n, round_number, None, None, False)
        # 1比特输入差分
        for diff_pos in range(cipher_block_size):
            plaintext_bits2 = copy.deepcopy(plaintext_bits1)
            plaintext_bits2[diff_pos] = plaintext_bits2[diff_pos] ^ 1
            _, ciphertext_bits2, _ = encrypt_n_rounds(round_structure, n, round_number, plaintext_bits2, round_keys_list)
            for linear_pos in range(cipher_block_size):
                z = ciphertext_bits1[linear_pos] ^ ciphertext_bits2[linear_pos]
                assert np.sum(z == 0) + np.sum(z == 1) == n
                cor = abs(2 * int(np.sum(z == 0)) / n - 1)
                if cor == 0:
                    cor = cor_t + 5
                else:
                    cor = abs(-1 * math.log2(cor))
                if cor <= cor_t:
                    diff_val = 1 << diff_pos
                    linear_val = 1 << linear_pos
                    tmp_collector.append((diff_val, linear_val, cor))
                    if cor < best_cor:
                        best_cor = cor
                        best_diff_val = diff_val
                        best_linear_val = linear_val

        if not tmp_collector:
            round_number -= 1
            break
        collector = tmp_collector
        print("找到{}条较好的{}轮差分线性".format(len(collector), round_number))
        round_number += 1
        best_short_diff_linear.append((best_diff_val, best_linear_val, best_cor))
    if len(collector) > max_diff_linear_num:
        collector.sort(key=lambda x: x[2])
        collector = collector[:max_diff_linear_num]
    return collector, round_number, best_short_diff_linear

# 执行SAT模型搜索时，添加条件：
# equal_constants: 令某些轮状态值等于给定常数，每一项格式为(约束第几轮状态，常数值)
# unequal_constants: 令某些轮状态值不等于给定常数，每一项格式为(约束第几轮状态，常数值)
def execute_SAT_with_constraints(cipher_body, cipher_block_size, round_number, counter_upper_bound, his_counter_upper_bound, is_search_diff, equal_constants, unequal_constants, with_upper_bound=True):
    global main_dl_cipher_name
    assert len(his_counter_upper_bound) >= round_number
    execute_index_sequence = sorted(cipher_body)
    clauses = []
    counter_variables_per_round = []
    counter_variables = []
    # 编号必须从1（非零）开始
    var_number = 1
    nodes_per_round = []
    round_nodes = []
    root_node = copy.deepcopy(cipher_body[execute_index_sequence[0]])
    if root_node.size != cipher_block_size:
        raise_error("轮函数起始ROOT节点状态应该与.CDFH声明的分组大小一致!")
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
    if with_upper_bound:
        var_number, tmp_clauses, s = sequential_encoding(var_number, counter_variables, counter_upper_bound)
        clauses += tmp_clauses
        clauses += add_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound)
    # 添加相等条件
    for round_index, constant in equal_constants:
        constraint = ConstantConstraint(round_index, list(range(cipher_block_size)), constant, "diff")
        var_number, tmp_clauses, _ = constraint.apply(var_number, round_nodes[round_index])
        clauses += tmp_clauses
    # 添加不等条件
    for round_index, constant in unequal_constants:
        constraint = UnequalConstantConstraint(round_index, list(range(cipher_block_size)), constant, "diff")
        var_number, tmp_clauses, _ = constraint.apply(var_number, round_nodes[round_index])
        clauses += tmp_clauses
    # 构造SAT求解器输入文件
    var_number -= 1
    SAT_input_path = SAT_util.SAT_tmp_folder + f"SAT_input_{main_dl_cipher_name}_dl_{round_number}_{counter_upper_bound}.cnf"
    SAT_output_path = SAT_util.SAT_tmp_folder + f"SAT_solution_{main_dl_cipher_name}_dl_{round_number}_{counter_upper_bound}.out"
    SAT_util.construct_dimacs_input(SAT_input_path, clauses, var_number)
    cmd_str = SAT_util.CaDiCaL_cmd + " " +  SAT_input_path + " > " + SAT_output_path
    res = subprocess.call(cmd_str, env=env_para, shell=True)
    # 判断是否SAT
    var_solution = SAT_util.get_var_solution(SAT_output_path)
    # 删除输入输出文件
    order = del_cmd + f" {SAT_input_path}"
    os.system(order)
    order = del_cmd + f" {SAT_output_path}"
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
    
def search_best_diff_linear(cipher_body, cipher_block_size, rest_round_number, collector, his_counter_upper_bound_diff, his_counter_upper_bound_linear, diff_search_his, linear_search_his, diff_cor_cache, linear_cor_cache):
    best_cor = 10000000
    for collector_index in range(len(collector)):
        diff_val, linear_val, mid_cor = collector[collector_index]
        for round_number_diff in range(0, rest_round_number + 1):
            cor = mid_cor
            if cor > best_cor:
                continue
            round_number_linear = rest_round_number - round_number_diff
            # 搜上面的差分部分
            if round_number_diff == 0:
                # 基部分
                diff_cor, input_diff = 0, diff_val
            elif round_number_diff + 1 <= len(diff_search_his[diff_val]):
                # 差分部分之前已经搜过
                diff_cor, input_diff = diff_search_his[diff_val][round_number_diff]
            else:
                # 差分部分要重新搜
                # 这个diff_val没必要再搜了
                if cor + diff_cor_cache[diff_val] > best_cor:
                    continue
                now_search_round_number = len(diff_search_his[diff_val])
                while True:
                    # 确保无约束的now_search_round_number轮差分路径搜过了
                    if now_search_round_number + 1 <= len(his_counter_upper_bound_diff):
                        diff_cor = his_counter_upper_bound_diff[now_search_round_number]
                    else:
                        # 先搜无约束的版本
                        assert now_search_round_number == len(his_counter_upper_bound_diff)
                        diff_cor = his_counter_upper_bound_diff[now_search_round_number - 1]
                        while True:
                            is_SAT, _, _ = execute_SAT_with_constraints(cipher_body, cipher_block_size, now_search_round_number, diff_cor, his_counter_upper_bound_diff, True, [], [])
                            if is_SAT:
                                break
                            diff_cor += 1
                        his_counter_upper_bound_diff.append(diff_cor)
                    if diff_cor_cache[diff_val] > diff_cor:
                        diff_cor = diff_cor_cache[diff_val]
                    while True:
                        is_SAT, round_nodes_solution, _ = execute_SAT_with_constraints(cipher_body, cipher_block_size, now_search_round_number, diff_cor, his_counter_upper_bound_diff, True, [(now_search_round_number, diff_val)], [])
                        if is_SAT:
                            input_diff = bits_to_int(round_nodes_solution[0])
                            assert bits_to_int(round_nodes_solution[-1]) == diff_val
                            diff_search_his[diff_val].append((diff_cor, input_diff))
                            break
                        if cor + diff_cor >= best_cor:
                            diff_cor += 1
                            break
                        diff_cor += 1
                    diff_cor_cache[diff_val] = diff_cor
                    if not is_SAT or now_search_round_number == round_number_diff:
                        break
                    now_search_round_number += 1
            cor += diff_cor
            if cor > best_cor:
                continue
            
            # 搜下面的线性部分
            if round_number_linear == 0:
                # 基部分
                linear_cor, output_linear = 0, linear_val
            elif round_number_linear + 1 <= len(linear_search_his[linear_val]):
                # 线性部分之前已经搜过
                linear_cor, output_linear = linear_search_his[linear_val][round_number_linear]
            else:
                # 线性部分要重新搜
                # 这个linear_val没必要再搜了
                if cor + 2 * linear_cor_cache[linear_val] > best_cor:
                    continue
                now_search_round_number = len(linear_search_his[linear_val])
                while True:
                    # 确保无约束的now_search_round_number轮线性路径搜过了
                    if now_search_round_number + 1 <= len(his_counter_upper_bound_linear):
                        linear_cor = his_counter_upper_bound_linear[now_search_round_number]
                    else:
                        # 先搜无约束的版本
                        assert now_search_round_number == len(his_counter_upper_bound_linear)
                        linear_cor = his_counter_upper_bound_linear[now_search_round_number - 1]
                        while True:
                            is_SAT, _, _ = execute_SAT_with_constraints(cipher_body, cipher_block_size, now_search_round_number, linear_cor, his_counter_upper_bound_linear, False, [], [])
                            if is_SAT:
                                break
                            linear_cor += 1
                        his_counter_upper_bound_linear.append(linear_cor)
                    if linear_cor_cache[linear_val] > linear_cor:
                        linear_cor = linear_cor_cache[linear_val]
                    while True:
                        is_SAT, round_nodes_solution, _ = execute_SAT_with_constraints(cipher_body,  cipher_block_size, now_search_round_number, linear_cor, his_counter_upper_bound_linear, False, [(0, linear_val)], [])
                        if is_SAT:
                            output_linear = bits_to_int(round_nodes_solution[-1])
                            assert bits_to_int(round_nodes_solution[0]) == linear_val
                            linear_search_his[linear_val].append((linear_cor, output_linear))
                            break
                        if cor + 2 * linear_cor >= best_cor:
                            linear_cor += 1
                            break
                        linear_cor += 1
                    linear_cor_cache[linear_val] = linear_cor
                    if not is_SAT or now_search_round_number == round_number_linear:
                        break
                    now_search_round_number += 1
                    
            cor += 2 * linear_cor
            
            # 更新最优值
            if cor < best_cor:
                best_cor = cor
                best_trail = (input_diff, round_number_diff, diff_cor, diff_val, linear_val, round_number_linear, linear_cor, output_linear, mid_cor)
                best_index = collector_index
    # 将搜到的最优路线对应的中间部分调到collector的最前面
    best_mid_trail = collector[best_index]
    del collector[best_index]
    collector.insert(0, best_mid_trail)
    return best_cor, best_trail

# 差分线性分析忽略约束部分
# 差分线性分析忽略轮函数前（.PREROUND）和轮函数后（.POSTROUND）结构，只对核心的轮函数进行搜索
# 差分线性分析采用迭代搜索，只能对轮函数中的一个循环体进行搜索
# 选择第search_loop_index个循环体，按照算法总轮数进行搜索
def do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number):
    global main_dl_cipher_name
    main_dl_cipher_name = cipher_name
    save_path = SAT_util.search_res_path(cipher_name, "diff_real")
    save_path = open(save_path, "w", buffering=1, encoding="utf-8")
    save_path.write("----------------------------------" + cipher_name + "密码的差分线性分析结果----------------------------------\n")
    his_counter_upper_bound_diff = [0]
    his_counter_upper_bound_linear = [0]
    diff_search_his = dict()
    linear_search_his = dict()
    diff_cor_cache = dict()
    linear_cor_cache = dict()
    cipher_body = cipher[2][0][search_loop_index]
    collector, mid_round_number, best_short_diff_linear = find_good_diff_liear_via_experiment(cipher_block_size, cipher_body)
    for i in range(1, mid_round_number + 1):
        print("找到一条{}轮差分线性路径, 相关性为2^-{:.2f}".format(i, best_short_diff_linear[i][2]))
        # 输出内容
        save_path.write("\n找到一条{}轮差分线性路径, 相关性为2^-{:.2f}:\n".format(i, best_short_diff_linear[i][2]))
        # 输出表头
        format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
        save_path.write(format_string.format("# Rounds", "Value Type", "Value", "Correlation"))
        # 输出内容
        format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
        save_path.write(format_string.format("", "Difference", best_short_diff_linear[i][0], ""))
        format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
        save_path.write(format_string.format(i, "Differential", "", "2^-{:.2f}".format(best_short_diff_linear[i][2])))
        format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
        save_path.write(format_string.format("", "Linear mask", best_short_diff_linear[i][1], ""))

    for diff_val, linear_val, cor in collector:
        if diff_val not in diff_search_his:
            diff_search_his[diff_val] = [(0, 0)]
            diff_cor_cache[diff_val] = 0
        if linear_val not in linear_search_his:
            linear_search_his[linear_val] = [(0, 0)]
            linear_cor_cache[linear_val] = 0
    for total_round_number in range(mid_round_number + 1, cipher_round_number + 1):
        best_cor, best_trail = search_best_diff_linear(cipher_body, cipher_block_size, total_round_number - mid_round_number, collector, his_counter_upper_bound_diff, his_counter_upper_bound_linear, diff_search_his, linear_search_his, diff_cor_cache, linear_cor_cache)
        print("找到一条{}轮差分线性路径, 相关性为2^-{:.2f}".format(total_round_number, best_cor))
        save_path.write("\n找到一条{}轮差分线性路径, 相关性为2^-{:.2f}:\n".format(total_round_number, best_cor))
        # 输出表头
        format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
        save_path.write(format_string.format("# Rounds", "Value Type", "Value", "Correlation"))
        # 输出内容
        if best_trail[1] > 0:
            format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
            save_path.write(format_string.format("", "Difference", best_trail[0], ""))
            format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
            save_path.write(format_string.format(best_trail[1], "Differential", "", "2^-{:.2f}".format(best_trail[2])))
        format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
        save_path.write(format_string.format("", "Difference", best_trail[3], ""))
        format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
        save_path.write(format_string.format(mid_round_number, "Differential-linear", "", "2^-{:.2f}".format(best_trail[8])))
        format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
        save_path.write(format_string.format("", "Linear mask", best_trail[4], ""))
        if best_trail[5] > 0:
            format_string = "| {:^8} | {:^20} | {:^" + str((cipher_block_size + 3) // 4 + 2) + "} | {:^13} |\n"
            save_path.write(format_string.format(best_trail[5], "Linear approximation", "", "(2^-{:.2f})^2".format(best_trail[6])))
            format_string = "| {:^8} | {:^20} | {:#0" + str((cipher_block_size + 3) // 4 + 2) + "x} | {:^13} |\n"
            save_path.write(format_string.format("", "Linear mask", best_trail[7], ""))
        if best_cor >= cipher_block_size:
            break
    save_path.close()