import numpy as np
import subprocess
import os
import SAT_util
from util import bits_to_int, assess_cmd, random_res_path
from node import *
from error_handler import raise_error
from encryption import encrypt
from hash import hash, get_message_per_round_structure


randomness_test_settings = {"n" : 1000000, "sample_num" : 100, "data_path" : "./test_data", "data_type_list" : ["low_density", "high_density", "random"], "pass_threshold":0, "hash_message_block_num_choice" : [1, 10], "data_density_pr" : 0.05}

def parse_write_test_res(save_file, res, sample_zero_num_list):
    e_to_c = {"Frequency":"频率测试", "BlockFrequency":"块内频率测试", "PokerDetect":"扑克检测", "Serial":"重叠子序列检测", "Runs":"游程总数检测", "RunsDistribution":"游程分布检测", "LongestRunOfOnes":"块内最大游程检测", "BinaryDerivate":"二元推导检测", "SelfCorrelation":"自相关检测", "Rank":"矩阵秩检测", "CumulativeSums-Forward":"前向累加和检测", "CumulativeSums-Backward":"后向累加和检测", "ApproximateEntropy":"近似熵检测", "LinearComplexity":"线性复杂度检测", "Universial":"通用检测", "DiscreteFourierTransform":"离散傅立叶检测"}
    n = randomness_test_settings["n"]
    sample_num = randomness_test_settings["sample_num"]
    wrong_number = 0
    # 输出总体频率统计信息
    # save_file.write("\n比特流简单统计信息:\n")
    # save_file.write("\n|  样本号  |  比特流的长度  |   取0比例   |   取1比例   |\n")
    # for sample_index in range(sample_num):
    #     zero_ratio = sample_zero_num_list[sample_index] / n
    #     save_file.write("| {:^7} | {:^12} | {:^10.6f} | {:^10.6f} |\n".format(sample_index, n, zero_ratio, 1 - zero_ratio))
    # 输出每个检测项结果
    # 输出全局参数
    res_index = 0
    res_len = len(res)
    for res_index in range(res_len):
        if res[res_index] == "Maxerror":
            max_error_number = int(res[res_index + 1])
            res_index += 2
            break
    save_file.write("\nALPHA = 0.01, max error sample number = {}\n".format(max_error_number))
    save_file.write("\n各项目检测结果:\n")
    # 表头
    save_file.write("\n| {:\u3000^10} |   通过检测的样本比例   |   {:\u3000^6}  |\n".format("检测项目", "是否合格"))
    while res_index < res_len:
        detect_name_ch = e_to_c[res[res_index]]
        error_number = int(res[res_index + 1])
        ratio_str = str(sample_num - error_number) + "/" + str(sample_num)
        res_index += 2
        save_file.write("| {:\u3000^10} |   {:^15}   |   {:\u3000^6}  |\n".format(detect_name_ch, ratio_str, "合格" if error_number <= max_error_number else "不合格"))
        if error_number > max_error_number:
            wrong_number += 1
    if wrong_number <= randomness_test_settings["pass_threshold"]:
        save_file.write("\n通过随机性检测!\n")
        return True
    else:
        save_file.write("\n未通过随机性检测!\n")
        return False


# 产生n个block_size比特的数据, 返回形状为(block_size, n), 数据类型为np.uint8的ndarray
# 低密和高密时保证n个分组不相同
# data_type可取["high_density", "low_density", "random"]
def generate_data_block(block_size, n, data_type="random"):
    if data_type == "random":
        data = np.frombuffer(os.urandom(block_size * n), dtype=np.uint8).reshape(block_size, n) & 1
        return data
    if data_type == "high_density":
        data = np.ones((n, block_size), dtype=np.uint8)
    else:
        data = np.zeros((n, block_size), dtype=np.uint8)
    block_index = 1
    hamming_weight = 1
    while block_index < n:
        assert hamming_weight <= block_size
        bit_pos = [i for i in range(hamming_weight)]
        while True:
            # 掩一个数据
            for pos in bit_pos:
                data[block_index][pos] ^= 1
            block_index += 1
            flag = hamming_weight - 1
            # 反向回溯
            while flag >= 0 and bit_pos[flag] == block_size + flag - hamming_weight:
                flag -= 1
            if flag == -1 or block_index == n:
                break
            bit_pos[flag] += 1
            for i in range(flag + 1, hamming_weight):
                bit_pos[i] = bit_pos[i - 1] + 1
        hamming_weight += 1
    data = np.transpose(data)
    return data

# 产生n个block_size比特的数据, 返回形状为(block_size, block_num), 数据类型为np.uint8的ndarray
# data_type可取["high_density", "low_density", "random"]
def generate_data_block_hash(block_size, block_num, data_type="random"):
    assert data_type in ["high_density", "low_density", "random"]
    pr = randomness_test_settings["data_density_pr"]
    pr_data = np.random.rand(block_size, block_num)
    output_data = np.zeros((block_size, block_num), dtype=np.uint8)
    if data_type == "random":
        return output_data | (pr_data > 0.5)
    if data_type == "low_density":
        return output_data | (pr_data < pr)
    if data_type == "high_density":
        return output_data | (pr_data > pr)

def randomness_test_block_cipher_ECB(cipher, cipher_name, cipher_block_size, cipher_round_number, subkey_expand_tuple, s):
    randomness_test_settings["sample_num"] = s
    # 须要保证cipher_block_size >= 16
    if cipher_block_size < 16:
        raise_error("正在进行分组密码随机性检测, ECB模式检测需要保证分组长度不小于16, 目前分组长度为{}!".format(cipher_block_size))
    print("进行分组密码ECB加密模式随机性检测, 生成数据流长度{}比特, 样本数据流{}个.".format(randomness_test_settings["n"], randomness_test_settings["sample_num"]))
    save_file = random_res_path(cipher_name)
    save_file = open(save_file, "w", encoding="utf-8")
    save_file.write("----------------------------------分组密码{}的ECB加密模式随机性检测----------------------------------\n".format(cipher_name))
    n = randomness_test_settings["n"]
    sample_num = randomness_test_settings["sample_num"]
    block_num = (n + cipher_block_size - 1) // cipher_block_size
    for data_type in randomness_test_settings["data_type_list"]:
        sample_zero_num_list = []
        data_tmp_file = randomness_test_settings["data_path"] + "_{}.data".format(cipher_name)
        f = open(data_tmp_file, "wb")
        ch_data_type = "随机数据"
        if data_type == "high_density":
            ch_data_type = "高密度数据"
        elif data_type == "low_density":
            ch_data_type = "低密度数据"
        print("\n检测数据流类型: {}, 正在生成检测数据...".format(ch_data_type))
        plaintext_bits = generate_data_block(cipher_block_size, block_num, data_type)
        for i in range(sample_num):
            if data_type == "random":
                plaintext_bits = generate_data_block(cipher_block_size, block_num, data_type)
            _, ciphertext_bits, _ = encrypt(cipher, cipher_round_number, cipher_block_size, subkey_expand_tuple, block_num, given_plaintext_bits=plaintext_bits, common_key=True)
            bit_string = np.array(ciphertext_bits).flatten('F')[:n]
            assert np.sum(bit_string == 0) + np.sum(bit_string == 1) == n
            sample_zero_num_list.append(np.sum(bit_string == 0))
            data = np.reshape(bit_string, (-1, 8))
            data = bits_to_int(np.transpose(data)).astype(np.uint8)
            f.write(data.tobytes())
        f.close()
        print("\n正在检测...")
        para_list = [assess_cmd, str(n), data_tmp_file, str(sample_num)]
        res = subprocess.check_output(para_list).decode().split()
        save_file.write("\n----------------------------------{}检测结果----------------------------------\n".format(ch_data_type))
        is_good = parse_write_test_res(save_file, res, sample_zero_num_list)
        print("\n检测完成! " + ("通过随机性检测!" if is_good else "未通过随机性检测!"))
    os.system(SAT_util.del_cmd + " " + data_tmp_file)
    save_file.close()

def randomness_test_hash_x_block(cipher, cipher_name, cipher_block_size, cipher_round_number, message_block_num, save_file, message_expand_tuple):
    save_file.write("\n----------------------------------{}个分组的消息的随机性检测----------------------------------\n".format(message_block_num))
    print("\n正在检测消息分组为{}时的随机性...".format(message_block_num))
    n = randomness_test_settings["n"]
    sample_num = randomness_test_settings["sample_num"]
    block_num = (n + cipher_block_size - 1) // cipher_block_size
    main_message_number = message_expand_tuple[4]
    main_message_size = message_expand_tuple[5]
    if main_message_number is None:
        # 按子消息节点的大小生成
        main_message_size_list = []
        message_per_round_structure, _ = get_message_per_round_structure(cipher, cipher_round_number)
        message_size_per_round = message_per_round_structure[1]
        for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
            main_message_size_list += message_size_per_round[i]
    else:
        # 按主消息节点的大小生成
        main_message_size_list = [main_message_size] * main_message_number
    # 随机生成一个固定的IV
    iv_bits = generate_data_block_hash(cipher_block_size, 1, "random").repeat(block_num, axis=1)
    for data_type in randomness_test_settings["data_type_list"]:
        sample_zero_num_list = []
        data_tmp_file = randomness_test_settings["data_path"] + "_{}.data".format(cipher_name)
        f = open(data_tmp_file, "wb")
        ch_data_type = "随机数据"
        if data_type == "high_density":
            ch_data_type = "高密度数据"
        elif data_type == "low_density":
            ch_data_type = "低密度数据"
        print("\n检测数据流类型: {}, 正在生成检测数据...".format(ch_data_type))
        for _ in range(sample_num):
            main_message_lists = []
            for _ in range(message_block_num):
                main_message_list = [generate_data_block_hash(message_size, block_num, data_type) for message_size in main_message_size_list]
                main_message_lists.append(main_message_list)
            _, _, digest_bits = hash(cipher, cipher_round_number, cipher_block_size, message_expand_tuple, block_num, message_block_num, iv_bits, main_message_lists)
            bit_string = np.array(digest_bits).flatten('F')[:n]
            assert np.sum(bit_string == 0) + np.sum(bit_string == 1) == n
            sample_zero_num_list.append(np.sum(bit_string == 0))
            data = np.reshape(bit_string, (-1, 8))
            data = bits_to_int(np.transpose(data)).astype(np.uint8)
            f.write(data.tobytes())
        f.close()
        print("\n正在检测...")
        para_list = [assess_cmd, str(n), data_tmp_file, str(sample_num)]
        res = subprocess.check_output(para_list).decode().split()
        save_file.write("\n----------------------------------{}检测结果----------------------------------\n".format(ch_data_type))
        is_good = parse_write_test_res(save_file, res, sample_zero_num_list)
        print("\n检测完成! " + ("通过随机性检测!" if is_good else "未通过随机性检测!"))

def randomness_test_hash(cipher, cipher_name, cipher_block_size, cipher_round_number, message_expand_tuple, block_num_list, s):
    randomness_test_settings["sample_num"] = s
    print("进行哈希算法随机性检测, 生成数据流长度{}比特, 样本数据流{}个.".format(randomness_test_settings["n"], randomness_test_settings["sample_num"]))
    save_file = random_res_path(cipher_name)
    save_file = open(save_file, "w", encoding="utf-8")
    save_file.write("----------------------------------哈希算法{}的随机性检测----------------------------------\n".format(cipher_name))
    if not block_num_list:
        block_num_list = randomness_test_settings["hash_message_block_num_choice"]
    for message_block_num in block_num_list:
        randomness_test_hash_x_block(cipher, cipher_name, cipher_block_size, cipher_round_number, message_block_num, save_file, message_expand_tuple)
    data_tmp_file = randomness_test_settings["data_path"] + "_{}.data".format(cipher_name)
    os.system(SAT_util.del_cmd + " " + data_tmp_file)
    save_file.close()