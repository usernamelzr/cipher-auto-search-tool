from node import *
from util import bits_to_int
import SAT_util
import copy
import subprocess
import os

main_idc_cipher_name = ""

def execute_SAT(cipher, round_number, input_diff=[],output_diff=[]):
    global main_idc_cipher_name
    execute_index_sequence = sorted(cipher)
    root_node = copy.deepcopy(cipher[execute_index_sequence[0]])
    assert isinstance(root_node, RootNode)
    # 只看第一个就行
    dec_cluase=[]
    clauses=[]
    indiff_cluase=idc_dec_diff(0,0,cipher[execute_index_sequence[0]].size,input_diff)
    outdiff_cluase=idc_dec_diff(execute_index_sequence[-1],round_number-1,cipher[execute_index_sequence[-1]].size,output_diff)
    for r in range(round_number):
        for index in execute_index_sequence:
            node = copy.deepcopy(cipher[index])
            dec_cluase += idc_gen_header_dec(node.idc_vardec_sentence(r))
    for r in range(round_number):
        for index in execute_index_sequence:
            node = copy.deepcopy(cipher[index])
            if isinstance(node, MergeNode) or isinstance(node, ParallelSBoxNode):
                parent_list = [copy.deepcopy(cipher[i]) for i in node.parent_index_list]
                tmp_clauses= node.idc_execute(r, parent_list)
                clauses += tmp_clauses
            elif isinstance(node, MessageNode) or isinstance(node, ImportNode):
                raise_error("不可能差分分析中不支持的节点类型: {}!".format(node.node_name))
            else:
                tmp_clauses= node.idc_execute(r)
                clauses += tmp_clauses
        if r < round_number-1:
            clauses += idc_passRound(r,execute_index_sequence[-1],execute_index_sequence[0],cipher[execute_index_sequence[0]].size)
    # 构造SAT求解器输入文件
    SAT_input_path = SAT_util.SAT_tmp_folder + "SAT_{}_idc_{}.txt".format(main_idc_cipher_name, round_number)
    # 判断是否SAT
    finput=open(SAT_input_path,"w")
    for item in dec_cluase:
        finput.write(item)
    for item in indiff_cluase:
        finput.write(item)
    for item in clauses:
        finput.write(item)
    for item in outdiff_cluase:
        finput.write(item)
    finput.write(idc_gen_end())
    finput.close()
    stp_parameters = [SAT_util.stp_cmd, "--minisat", "--CVC", SAT_input_path]
    res = subprocess.check_output(stp_parameters, env=env_para)
    res = res.replace(b"\r", b"")[0:-1].decode()
    order = del_cmd + f" {SAT_input_path}"
    os.system(order)
    if (res.endswith("Valid.")):
        return True
    return False
    
def generate_diff_under_hamming_bound(cipher_block_size, hamming_upbound):
    res = []
    hamming_weight = 1
    while hamming_weight <= hamming_upbound:
        bit_pos = [i for i in range(hamming_weight)]
        while True:
            diff_val = [0] * cipher_block_size
            for pos in bit_pos:
                diff_val[pos] = 1
            res.append(diff_val)
            flag = hamming_weight - 1
            while flag >= 0 and bit_pos[flag] == cipher_block_size + flag - hamming_weight:
                flag -= 1
            if flag == -1:
                break
            bit_pos[flag] += 1
            for i in range(flag + 1, hamming_weight):
                bit_pos[i] = bit_pos[i - 1] + 1
        hamming_weight += 1
    return res

def generate_diff_pool_rc5(cipher_block_size):
    word_size = cipher_block_size // 2
    diff_pool_input = []
    for i in range(word_size):
        diff_val = [0] * cipher_block_size
        diff_val[i] = 1
        diff_val[i + word_size] = 1
        diff_pool_input.append(diff_val)
    diff_pool_output = []
    for i in range(cipher_block_size):
        diff_val = [0] * cipher_block_size
        diff_val[i] = 1
        diff_pool_output.append(diff_val)
    return diff_pool_input, diff_pool_output

def do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number,Hamming_upbond):
    global main_idc_cipher_name
    main_idc_cipher_name = cipher_name
    cipher_body = cipher[2][0][search_loop_index]
    round_number = 1
    save_path = SAT_util.search_res_path(cipher_name, "real")
    save_path = open(save_path, "w", buffering=1, encoding="utf-8")
    print("\n尝试汉明重量不大于{}的输入输出差分对.".format(Hamming_upbond))
    save_path.write("----------------------------------" + cipher_name + "密码的不可能差分分析结果----------------------------------\n")
    diff_value_pool = generate_diff_under_hamming_bound(cipher_block_size, Hamming_upbond)
    diff_value_pool_input = diff_value_pool
    diff_value_pool_output = diff_value_pool
    # diff_value_pool_input, diff_value_pool_output = generate_diff_pool_rc5(cipher_block_size)
    while round_number <= cipher_round_number:
        print("\n正在搜索{}轮的不可能差分特征...".format(round_number))
        for input_diff in diff_value_pool_input:
            for output_diff in diff_value_pool_output:
                answer = execute_SAT(cipher_body, round_number, input_diff, output_diff)
                if answer:
                    round_num_str = "{} Rounds".format(round_number)
                    blank_str = " " * len(round_num_str)
                    mid_str_len = 5 + 2 * len(round_num_str)
                    save_path.write("\n找到一条{}轮不可能差分特征:\n".format(round_number))
                    input_diff_int = bits_to_int(input_diff, False)
                    output_diff_int = bits_to_int(output_diff, False)
                    format_string = "| {:^" + str(max((cipher_block_size + 3) // 4 + 2, mid_str_len)) +"} |\n"
                    format_string_int = "{:#0" + str((cipher_block_size + 3) // 4 + 2) + "x}"
                    save_path.write("\n" + format_string.format(format_string_int.format(input_diff_int)))
                    save_path.write(format_string.format(blank_str + "  |  " + blank_str))
                    save_path.write(format_string.format(blank_str + "  |  " + blank_str))
                    save_path.write(format_string.format(blank_str + "  |  " + round_num_str))
                    save_path.write(format_string.format(blank_str + "  |  " + blank_str))
                    save_path.write(format_string.format(blank_str + r"\ | /" + blank_str))
                    save_path.write(format_string.format(blank_str + r" \|/ " + blank_str))
                    save_path.write(format_string.format(format_string_int.format(output_diff_int)))
                    print("\n找到一条{}轮不可能差分特征!".format(round_number))
                    break
            if answer:
                break
        if not answer:
            print("\n不存在汉明重量不大于{}的{}轮不可能差分特征!".format(Hamming_upbond, round_number))
            save_path.write("\n不存在汉明重量不大于{}的{}轮不可能差分特征!\n".format(Hamming_upbond, round_number))
            break
        round_number += 1
    save_path.close()