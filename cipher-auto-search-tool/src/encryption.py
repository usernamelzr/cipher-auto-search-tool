from node import *
import numpy as np
import os

# round key为一轮用到的所有轮密钥列表（考虑到了轮函数内可能有多个子密钥参与）
def encrypt_one_round(round_structure, input_state, execute_index_sequence, round_keys, round_index, states_his):
    pre_round_states, states_per_round, post_round_states = states_his
    states = dict()
    root_index = execute_index_sequence[0]
    assert isinstance(round_structure[root_index], RootNode)
    states[root_index] = input_state
    round_key_index = 0
    for index in execute_index_sequence[1:]:
        node = round_structure[index]
        if isinstance(node, SplitNode) or isinstance(node, BranchNode) or isinstance(node, SBoxNode) or isinstance(node, PNode) or isinstance(node, EqualNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
        elif isinstance(node, ConstantNode):
            states[index] = node.pass_state(round_index)
        elif isinstance(node, RotationNode) or isinstance(node, ShiftNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state, round_index)
        elif isinstance(node, MergeNode) or isinstance(node, FNode) or isinstance(node, XORNode):
            input_states_list = [states[i] for i in node.parent_index_list]
            states[index] = node.pass_state(input_states_list)
        elif isinstance(node, AddNode):
            input_state1 = states[node.parent_index1]
            input_state2 = states[node.parent_index2]
            states[index] = node.pass_state(input_state1, input_state2)
        elif isinstance(node, SubKeyNode):
            states[index] = node.pass_state(round_keys[round_key_index])
            round_key_index += 1
        elif isinstance(node, ParallelSBoxNode):
            parent_input_list = [states[parent_index] for parent_index in node.parent_index_list]
            output_list = node.pass_state(parent_input_list)
            if output_list:
                for i in range(node.output_length):
                    states[node.output_index_list[i]] = output_list[i]
        elif isinstance(node, EndNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
            output_state = states[index]
        elif isinstance(node, VarRotationNode):
            input_value = states[node.parent_index]
            input_case = states[node.case_index]
            states[index] = node.pass_state(input_value, input_case)
        elif isinstance(node, ImportNode):
            if states_per_round is None:
                raise_error("差分线性分析轮函数结构中不支持IMPORT节点!")
            if node.round_index >= 0:
                tstates = states_per_round[node.round_index]
                if node.index_in_round not in tstates:
                    raise_error("IMPORT引用了轮函数中不存在的节点! IMPORT节点编号{}, 引用了第{}轮的节点{}!".format(node.index, node.round_index, node.index_in_round))
                states[index] = node.pass_state(tstates[node.index_in_round])
            elif node.round_index == -2:
                if node.index_in_round not in pre_round_states:
                    raise_error("IMPORT引用了PREROUND部分中不存在的节点! IMPORT节点编号{}, 引用了PREROUND的节点{}!".format(node.index, node.index_in_round))
                states[index] = node.pass_state(pre_round_states[node.index_in_round])
            else:
                assert node.round_index < -2
                target_round_index = round_index + 2 + node.round_index
                if target_round_index < 0:
                    raise_error("第{}轮的IMPORT节点{}引用了第{}轮的节点!".format(round_index, node.index, target_round_index))
                tstates = states_per_round[target_round_index]
                if node.index_in_round not in tstates:
                    raise_error("IMPORT引用了轮函数中不存在的节点! IMPORT节点编号{}, 引用了第{}轮的节点{}!".format(node.index, target_round_index, node.index_in_round))
                states[index] = node.pass_state(tstates[node.index_in_round])
        elif isinstance(node, MessageNode):
            raise_error("正在加密中, 分组密码中无法解析消息节点, 节点编号为{}!".format(index))
        else:
            raise_error("正在加密中, 解析到未支持的{}节点! 节点编号为{}.".format(node.node_name, index))
    return output_state, states

# 只执行n次单一的round_structure, 目前只用于差分线性分析
def encrypt_n_rounds(round_structure, n, round_number, given_plaintext_bits=None, given_round_keys_list=None, common_key=False):
    execute_index_sequence = sorted(round_structure)
    root_node = round_structure[execute_index_sequence[0]]
    assert isinstance(root_node, RootNode)
    # 统计每轮使用到的子密钥信息
    round_keys_size = []
    for index in execute_index_sequence[1:]:
        node = round_structure[index]
        if isinstance(node, SubKeyNode):
            round_keys_size.append(node.size)
    if given_round_keys_list is None:
        round_keys_list = []
        for _ in range(round_number):
            round_keys = []
            for i in round_keys_size:
                if common_key:
                    round_keys.append(np.frombuffer(os.urandom(i), dtype=np.uint8).reshape(i, 1) & 1)
                else:
                    round_keys.append(np.frombuffer(os.urandom(i * n), dtype=np.uint8).reshape(i, n) & 1)
            round_keys_list.append(round_keys)
    else:
        assert len(given_round_keys_list) == round_number and len(given_round_keys_list[0]) == len(round_keys_size)
        round_keys_list = given_round_keys_list
    if given_plaintext_bits is None:
        plaintext_bits = root_node.pass_state(n)
    else:
        plaintext_bits = given_plaintext_bits
    ciphertext_bits = plaintext_bits
    for i in range(round_number):
        ciphertext_bits, _ = encrypt_one_round(round_structure, ciphertext_bits, execute_index_sequence, round_keys_list[i], i, (None, None, None))
    return plaintext_bits, ciphertext_bits, round_keys_list

def subkey_expand(subkey_expand_tuple, main_key_list):
    subkey_expand_structure = subkey_expand_tuple[0]
    execute_index_sequence = sorted(subkey_expand_structure)
    subkey_indexes = subkey_expand_tuple[1]
    main_key_number = subkey_expand_tuple[4]
    if not subkey_indexes:
        # 用户并没有给出密钥扩展规则, 此时直接使用主密钥作为每轮进入的子密钥
        return main_key_list
    if main_key_number != len(main_key_list):
        raise_error("用户提供的主密钥节点数与密钥扩展规则中的声明不一致! 提供了{}个主密钥字, 需要{}个主密钥字.".format(len(main_key_list), main_key_number))
    states = dict()
    for index in execute_index_sequence:
        node = subkey_expand_structure[index]
        if isinstance(node, SplitNode) or isinstance(node, BranchNode) or isinstance(node, SBoxNode) or isinstance(node, PNode) or isinstance(node, EqualNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
        elif isinstance(node, RotationNode) or isinstance(node, ShiftNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
        elif isinstance(node, MergeNode) or isinstance(node, FNode) or isinstance(node, XORNode):
            input_states_list = [states[i] for i in node.parent_index_list]
            states[index] = node.pass_state(input_states_list)
        elif isinstance(node, SubKeyNode):
            if index >= main_key_number:
                raise_error("正在执行密钥扩展部分, 密钥扩展规则不能定义SUBKEY节点!")
            states[index] = node.pass_state(main_key_list[index])
        elif isinstance(node, ConstantNode):
            states[index] = node.pass_state(0)
        elif isinstance(node, VarRotationNode):
            input_value = states[node.parent_index]
            input_case = states[node.case_index]
            states[index] = node.pass_state(input_value, input_case)
        elif isinstance(node, AddNode):
            input_state1 = states[node.parent_index1]
            input_state2 = states[node.parent_index2]
            states[index] = node.pass_state(input_state1, input_state2)
        elif isinstance(node, ParallelSBoxNode):
            parent_input_list = [states[parent_index] for parent_index in node.parent_index_list]
            output_list = node.pass_state(parent_input_list)
            if output_list:
                for i in range(node.output_length):
                    states[node.output_index_list[i]] = output_list[i]
        else:
            raise_error("正在进行消息扩展, 解析到未支持的{}节点! 节点编号为{}.".format(node.node_name, index))
    subkey_list = [states[i] for i in subkey_indexes]
    return subkey_list

def get_round_key_structure(cipher, cipher_round_number):
    pre_round, post_round, cipher_bodys, cipher_body_loop_num = cipher[0], cipher[1], cipher[2][0], cipher[2][1]
    # 将所有循环体串联起来
    loop_num = len(cipher_body_loop_num)
    round_structure_list = []
    execute_sequence_list = []
    for i in range(loop_num):
        execute_sequence = sorted(cipher_bodys[i])
        for _ in range(cipher_body_loop_num[i]):
            round_structure_list.append(cipher_bodys[i])
            execute_sequence_list.append(execute_sequence)
    round_keys_size = dict()
    round_key_num = 0
    for i in range(-2, cipher_round_number):
        round_keys_size[i] = []
    if pre_round:
        for index in sorted(pre_round):
            node = pre_round[index]
            if isinstance(node, SubKeyNode):
                round_keys_size[-2].append(node.size)
                round_key_num += 1
    for i in range(cipher_round_number):
        for index in execute_sequence_list[i]:
            node = round_structure_list[i][index]
            if isinstance(node, SubKeyNode):
                round_keys_size[i].append(node.size)
                round_key_num += 1
    if post_round:
        for index in sorted(post_round):
            node = post_round[index]
            if isinstance(node, SubKeyNode):
                round_keys_size[-1].append(node.size)
                round_key_num += 1
    return (round_key_num, round_keys_size), (round_structure_list, execute_sequence_list)

# 轮前和轮后都执行, 允许存在多个循环体
def encrypt(cipher, cipher_round_number, cipher_block_size, subkey_expand_tuple, n, given_plaintext_bits=None, given_round_keys=None, given_main_key_list=None, common_key=False):
    pre_round, post_round = cipher[0], cipher[1]
    round_key_structure, cipher_body_structure = get_round_key_structure(cipher, cipher_round_number)
    round_key_num, round_keys_size = round_key_structure
    round_structure_list, execute_sequence_list = cipher_body_structure
    main_key_number = subkey_expand_tuple[4]
    main_key_size = subkey_expand_tuple[5]
    if given_round_keys is not None:
        # 直接使用提供的轮密钥
        round_keys = given_round_keys
    else:
        if given_main_key_list is None:
            # 需要随机生成密钥
            if main_key_number is not None:
                # 用户给出了密钥扩展规则, 只需要随机生成主密钥列表即可
                if common_key:
                    main_key_list = np.frombuffer(os.urandom(main_key_number * main_key_size), dtype=np.uint8).reshape((main_key_number, main_key_size, 1)) & 1
                else:
                    main_key_list = np.frombuffer(os.urandom(main_key_number * main_key_size * n), dtype=np.uint8).reshape((main_key_number, main_key_size, n)) & 1
            else:
                # 用户没有给出密钥扩展规则, 需要随机生成每轮子密钥
                main_key_list = []
                for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
                    for subkey_size in round_keys_size[i]:
                        if common_key:
                            main_key_list.append(np.frombuffer(os.urandom(subkey_size), dtype=np.uint8).reshape(subkey_size, 1).repeat(n, axis=1) & 1)
                        else:
                            main_key_list.append(np.frombuffer(os.urandom(subkey_size * n), dtype=np.uint8).reshape(subkey_size, n) & 1)
        else:
            # 检查: 用户给出的密钥列表长度应当满足要求
            if main_key_number is None and len(given_main_key_list) != round_key_num:
                raise_error("算法没有密钥扩展结构, 用户提供的主密钥字数({})必须与算法需要的子密钥数({})一致!".format(len(given_main_key_list), round_key_num))
            elif main_key_number is not None and len(given_main_key_list) != main_key_number:
                raise_error("算法存在密钥扩展结构, 用户提供的主密钥字数({})必须与消息扩展部分定义({})一致!".format(len(given_main_key_list), main_key_number))
            # 用户已经给出了主密钥列表, 但是用户给出的主密钥是整数形式, 需要转换为比特数组的形式
            if round_key_num > 0 and isinstance(given_main_key_list[0], int):     
                main_key_list = []       
                if main_key_number is None:
                    # 没有密钥扩展结构, 按照每个子密钥的长度转换   
                    main_key_index = 0
                    for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
                        for subkey_size in round_keys_size[i]:
                            main_key_list.append(int_to_bits(given_main_key_list[main_key_index], subkey_size, False))
                            main_key_index += 1
                else:
                    # 存在密钥扩展结构, 按照主密钥长度转换
                    for main_key_int in given_main_key_list:
                        main_key_list.append(int_to_bits(main_key_int, main_key_size, False))
            else:
                main_key_list = given_main_key_list
        # 进行密钥扩展
        subkey_list = subkey_expand(subkey_expand_tuple, main_key_list)
        if len(subkey_list) != round_key_num:
            raise_error("轮函数扩展规则生成的子密钥数({})与轮函数体需要的子密钥数({})不一致!".format(len(subkey_list), round_key_num))
        # for subkey in subkey_list:
        #     subkey = bits_to_int(subkey)
        #     print(hex(subkey))
        # 将子密钥结构化到每一轮中
        round_keys = dict()
        index_in_subkey_list = 0
        for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
            round_keys[i] = []
            for subkey_size in round_keys_size[i]:
                round_keys[i].append(subkey_list[index_in_subkey_list])
                index_in_subkey_list += 1
    if given_plaintext_bits is None:
        plaintext_bits = np.frombuffer(os.urandom(cipher_block_size * n), dtype=np.uint8).reshape(cipher_block_size, n) & 1
    else:
        plaintext_bits = given_plaintext_bits
    pre_round_states = None
    post_round_states = None
    states_per_round = []
    if pre_round:
        execute_sequence = sorted(pre_round)
        plaintext_bits, pre_round_states = encrypt_one_round(pre_round, plaintext_bits, execute_sequence, round_keys[-2], 0, (pre_round_states, states_per_round, post_round_states))
    ciphertext_bits = plaintext_bits
    for i in range(cipher_round_number):
        ciphertext_bits, states = encrypt_one_round(round_structure_list[i], ciphertext_bits, execute_sequence_list[i], round_keys[i], i, (pre_round_states, states_per_round, post_round_states))
        states_per_round.append(states)
    if post_round:
        execute_sequence = sorted(post_round)
        ciphertext_bits, post_round_states = encrypt_one_round(post_round, ciphertext_bits, execute_sequence, round_keys[-1], 0, (pre_round_states, states_per_round, post_round_states))
    return plaintext_bits, ciphertext_bits, round_keys