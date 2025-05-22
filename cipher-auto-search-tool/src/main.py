import os
import shutil
import main_d_l
import main_dl
import main_idc
import main_hash
import verify
import randomness_test
import re
import time
import SAT_util
from configparser import ConfigParser
from cipher_parser import parse_cipher_description_file, find_whether_with_add, find_large_sbox
from error_handler import raise_error
from util import random_res_path
from hash import get_message_per_round_structure
from encryption import get_round_key_structure

if __name__ == "__main__":
    # 加载配置文件
    conf = ConfigParser()
    conf.read("config.ini")
    # 确定运行系统
    if not conf.has_option("system level", "system"):
        raise_error("config.ini中找不到[system level]system参数!")
    system_type = conf["system level"]["system"]
    SAT_util.set_cmd_str(system_type)
    if not os.path.isdir("bin"):
        shutil.copytree("..{0}bin_{1}".format(SAT_util.file_path_separator, system_type), "bin")
        os.chmod(SAT_util.CaDiCaL_cmd, 0o777)
        if os.path.exists(SAT_util.stp_cmd):
            os.chmod(SAT_util.stp_cmd, 0o777)
        os.chmod(SAT_util.espresso_cmd, 0o777)
    # 确定结果保存文件
    if conf.has_option("log file path", "result_folder"):
        SAT_util.set_search_result_folder(conf["log file path"]["result_folder"])
    if not os.path.isdir(SAT_util.search_result_folder):
        os.makedirs(SAT_util.search_result_folder)
    if not os.path.isdir("SAT_tmp"):
        os.makedirs("SAT_tmp")

    # 交互程序
    print("\n----------------------------------商用密码分析程序----------------------------------\n\n")

    print("分析选项:\n")
    print("[1] {:\u3000<10}    [2] {}".format("差分分析", "线性分析"))
    print("[3] {:\u3000<10}    [4] {}".format("差分线性分析", "不可能差分分析"))
    print("[5] {:\u3000<10}    [6] {}".format("哈希碰撞搜索", "算法随机性检测"))
    print("[7] {:\u3000<10}".format("算法实现正确性检测"))
    analysis_category = input("\n请选择分析项目(输入1~7): ")
    analysis_category = int(analysis_category)
    if analysis_category < 1 or analysis_category > 7:
        raise_error("\n项目编号有误!")
    if analysis_category == 1:
        search_type = "diff"
    elif analysis_category == 2:
        search_type = "linear"
    elif analysis_category == 3:
        search_type = "diff_linear"
    elif analysis_category == 4:
        search_type = "real"
    elif analysis_category == 5:
        search_type = "diff_real"
    else:
        search_type = "other"

    cipher_path = input("\n请输入算法描述文件路径(.cdf文件)或算法名称(默认在./cipher文件夹中): ")
    if cipher_path.endswith(".cdf"):
        cipher_name = re.split(r'\\|/', cipher_path)[-1][:-4]
    else:
        cipher_name = cipher_path
        cipher_path = "./cipher/" + cipher_name + ".cdf"
    if not os.path.isfile(cipher_path):
        raise_error("\n算法描述文件路径错误!")
    
    whether_consider_pr = True
    if analysis_category == 1 or analysis_category == 2:
        find_add = find_whether_with_add(cipher_path)
        if not find_add:
            whether_has_large_sbox, whether_has_sbox = find_large_sbox(cipher_path)
            if whether_has_large_sbox:
                print("\n[警告] 解析到算法中存在大状态S盒, 表示S盒概率模型可能耗时较长, 建议只搜索活跃S盒数量!\n")
            if whether_has_sbox:
                input_int = input("\n模型中是否只搜索活跃S盒数量(请输入数字, 1表示是, 0表示否, 输入回车默认为0):")
                if input_int.isdigit():
                    input_int = int(input_int)
                    if input_int != 0 and input_int != 1:
                        raise_error("选项输入有误, 只能输入0或1!")
                    if input_int == 1:
                        whether_consider_pr = False

    print("\n正在解析算法...")

    cipher_info, cipher, constraint_info, message_expand_info = parse_cipher_description_file(cipher_path, search_type, whether_consider_pr)
    cipher_category, cipher_round_number, cipher_block_size = cipher_info
    print("\n算法加载完成! 解析到{}密码算法{}!".format("分组" if cipher_category == "block" else "哈希", cipher_name))

    if analysis_category in [1, 2, 3, 4]:
        if len(cipher[2][0]) == 1:
            search_loop_index = 0
        else:
            search_loop_index = input("\n轮函数中共解析到{}个循环体, 要分析第几个循环体, 序号从0开始(如果默认分析首个循环体, 不用关心此选项直接输入回车即可): ".format(len(cipher[2][0])))
            if not search_loop_index.isdigit():
                search_loop_index = 0
            else:
                search_loop_index = int(search_loop_index)
                cipher_loop_num = len(cipher[2][1])
                if search_loop_index >= cipher_loop_num:
                    raise_error("循环体序号超出范围!")
    elif analysis_category == 5:
        if cipher_category == "block":
            raise_error("分组密码算法不支持搜索碰撞攻击!")
        round_number = input("\n请输入要搜索的轮数(默认搜索全轮, 不关心此选项直接输入回车即可): ")
        if not round_number.isdigit():
            round_number = cipher_round_number
        else:
            round_number = int(round_number)
        assert round_number <= cipher_round_number
    
    if analysis_category == 4:
        hamming_upbound = input("\n请输入输入输出差分汉明重量的最大值(默认为1, 直接输入回车使用默认值): ")
        if not hamming_upbound.isdigit():
            hamming_upbound = 1
        else:
            hamming_upbound = int(hamming_upbound)

    if analysis_category == 6:
        s = input("\n请输入要检测的样本数, (直接输入回车采用默认值1000): ")
        if not s.isdigit():
            s = 1000
        else:
            s = int(s)
    
    if analysis_category >= 1 and analysis_category <= 5:
        print("\n正在进行安全性分析...\n")
        print("详细路线信息请查看文件 " + SAT_util.search_res_path(cipher_name, search_type, whether_consider_pr) + "\n")
        start = time.time()
        if analysis_category == 1:
            main_d_l.do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number, constraint_info, True, whether_consider_pr)
        elif analysis_category == 2:
            main_d_l.do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number, constraint_info, False, whether_consider_pr)
        elif analysis_category == 3:
            main_dl.do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number)
        elif analysis_category == 4:
            main_idc.do_cryptanalysis(cipher, cipher_name, search_loop_index, cipher_block_size, cipher_round_number, hamming_upbound)
        elif analysis_category == 5:
            main_hash.do_cryptanalysis(cipher, cipher_name, cipher_block_size, round_number, constraint_info, message_expand_info)
        end = time.time()
        print("\n分析完成!")
        print("\n运行时间: {}s".format(end - start))
    elif analysis_category == 6:
        if cipher_category == "block":
            print("\n正在进行随机性检测...\n")
            print("检测结果请查看文件 " + random_res_path(cipher_name) + "\n")
            start = time.time()
            randomness_test.randomness_test_block_cipher_ECB(cipher, cipher_name, cipher_block_size, cipher_round_number, message_expand_info, s)
            end = time.time()
            print("\n分析完成!")
            print("\n运行时间: {}s".format(end - start))
        else:
            block_num_list_str = input("\n每次哈希要处理多少个消息分组, 请输入一个或多个数字(多个数字用空格分隔, 如果采用默认设置(每次处理1个和10个消息块)请直接输入回车): ")
            block_num_str_list = block_num_list_str.split()
            block_num_list = []
            for block_num_str in block_num_str_list:
                block_num_list.append(int(block_num_str))
            print("\n正在进行随机性检测...\n")
            print("检测结果请查看文件 " + random_res_path(cipher_name) + "\n")
            start = time.time()
            randomness_test.randomness_test_hash(cipher, cipher_name, cipher_block_size, cipher_round_number, message_expand_info, block_num_list, s)
            end = time.time()
            print("\n分析完成!")
            print("\n运行时间: {}s".format(end - start))
    elif analysis_category == 7:
        print("\n检测向量输入方式:")
        print("\n[1] {:\u3000<10}    [2] {}".format("文件输入", "手动输入"))
        input_approach = input("\n请选择检测向量的输入方式(输入1或2): ")
        if not input_approach.isdigit():
            raise_error("输入选项有误!")
        input_approach = int(input_approach)
        if input_approach not in [1, 2]:
            raise_error("输入选项有误!")
        if input_approach == 2:
            if cipher_category == "block":
                # 分组密码
                round_key_num = get_round_key_structure(cipher, cipher_round_number)[0][0]
                plaintext_str = input("\n请输入一个明文, 长度为{}比特(建议用十六进制, 数值以0x开头): ".format(cipher_block_size))
                main_key_number = message_expand_info[4]
                main_key_size = message_expand_info[5]
                if main_key_number is not None:
                    main_key_list_str = input("\n算法定义了密钥扩展, 请依次输入{}个主密钥, 每个值{}比特(用空格分隔): ".format(main_key_number, main_key_size))
                    main_key_list_len = main_key_number
                else:
                    main_key_list_str = input("\n算法没有定义密钥扩展, 请依次输入轮函数中用到的{}个密钥节点值(包括PREROUND和POSTROUND结构中的密钥节点, 用空格分隔, 若一轮输入了多个密钥节点, 按照其轮内编号从小到大依次给出): ".format(round_key_num))
                    main_key_list_len = round_key_num
                ciphertext_str = input("\n请输入对应的密文值, 长度为{}比特(若不给出密文可直接输入回车): ".format(cipher_block_size))
                # 解析检测向量字符串
                plaintext_str = plaintext_str.strip()
                plaintext_int = int(plaintext_str, base=0)
                main_key_str_list = main_key_list_str.split()
                if len(main_key_str_list) != main_key_list_len:
                    raise_error("输入的密钥数量不符合! 解析到{}个密钥, 需要{}个密钥!".format(len(main_key_str_list), main_key_list_len))
                main_key_list = []
                for main_key_str in main_key_str_list:
                    main_key_list.append(int(main_key_str, base=0))
                ciphertext_str = ciphertext_str.strip()
                if ciphertext_str:
                    ciphertext_int = int(ciphertext_str, base=0)
                else:
                    ciphertext_int = None
                verify.verify_block_cipher(plaintext_int, main_key_list, ciphertext_int, cipher, cipher_round_number, cipher_block_size, message_expand_info)
            else:
                # 哈希函数
                iv_str = input("\n请输入一个初始向量IV值, 长度为{}比特(建议用十六进制, 数值以0x形状): ".format(cipher_block_size))
                main_message_number = message_expand_info[4]
                main_message_size = message_expand_info[5]
                if main_message_number is not None:
                    main_message_list_str = input("\n算法定义了消息扩展, 请依次输入{}个主消息, 每个值{}比特(用空格分隔): ".format(main_message_number, main_message_size))
                    message_list_len = main_message_number
                else:
                    # 用户需要输入子消息
                    message_list_len = get_message_per_round_structure(cipher, cipher_round_number)[0][0]
                    main_message_list_str = input("\n算法没有定义消息扩展, 请依次输入轮函数中用到的{}个消息节点值(包括PREROUND和POSTROUND结构中的消息节点, 用空格分隔, 若一轮输入了多个消息节点, 按照其轮内编号从小到大依次给出): ".format(message_list_len))
                digest_str = input("\n请输入对应的消息摘要(哈希算法结果), 长度为{}比特(若不提供消息摘要可直接输入回车): ".format(cipher_block_size))
                # 解析测试向量字符串
                iv_str = iv_str.strip()
                iv_int = int(iv_str, base=0)
                main_message_str_list = main_message_list_str.split()
                if len(main_message_str_list) != message_list_len:
                    raise_error("输入的消息数量不符合! 解析到{}个消息, 需要{}个消息!".format(len(main_message_str_list), message_list_len))
                main_message_list = []
                for main_message_str in main_message_str_list:
                    main_message_list.append(int(main_message_str, base=0))
                digest_str = digest_str.strip()
                if digest_str:
                    digest_int = int(digest_str, base=0)
                else:
                    digest_int = None
                verify.verify_hash(iv_int, main_message_list, digest_int, cipher, cipher_round_number, cipher_block_size, message_expand_info)
        else:
            check_path = input("\n请输入测试向量文件路径或输入回车选择默认路径(./cipher/testvector/{}.check): ".format(cipher_name))
            check_path = check_path.strip()
            if not check_path:
                check_path = "./cipher/testvector/{}.check".format(cipher_name)
            if not os.path.isfile(check_path):
                raise_error("\n算法测试向量文件路径错误!")
            print("\n测试向量文件路径:", check_path)
            if cipher_category == "block":
                # 分组密码
                plaintext_int, main_key_list, ciphertext_int = verify.parse_testvector_file_block_cipher(check_path)
                verify.verify_block_cipher(plaintext_int, main_key_list, ciphertext_int, cipher, cipher_round_number, cipher_block_size, message_expand_info)
            else:
                # HASH
                iv_int, message_list, digest_int = verify.parse_testvector_file_hash(check_path)
                verify.verify_hash(iv_int, message_list, digest_int, cipher, cipher_round_number, cipher_block_size, message_expand_info)
