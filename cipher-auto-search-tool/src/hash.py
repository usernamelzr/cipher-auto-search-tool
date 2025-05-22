from node import *

def hash_one_round(round_structure, input_state, execute_index_sequence, messages, round_index, states_his):
    pre_round_states, states_per_round, post_round_states = states_his
    states = dict()
    message_index = 0
    root_index = execute_index_sequence[0]
    assert isinstance(round_structure[root_index], RootNode)
    states[root_index] = input_state
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
        elif isinstance(node, MessageNode):
            states[index] = node.pass_state(messages[message_index])
            message_index += 1
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
        elif isinstance(node, SubKeyNode):
            raise_error("正在计算哈希函数值, 哈希算法中不支持密钥节点! 节点编号为{}.".format(index))
        else:
            raise_error("正在计算哈希函数值, 解析到未支持的{}节点! 节点编号为{}.".format(node.node_name, index))
    return output_state, states

def message_expand(message_expand_tuple, main_message_list):
    message_expand_structure = message_expand_tuple[0]
    execute_index_sequence = sorted(message_expand_structure)
    message_indexes = message_expand_tuple[1]
    main_message_number = message_expand_tuple[4]
    if not message_indexes:
        # 用户并没有给出消息扩展规则, 此时直接使用主消息作为每轮进入的子消息
        return main_message_list
    if main_message_number != len(main_message_list):
        raise_error("用户提供的主消息节点数与消息扩展规则中的声明不一致! 提供了{}个主消息节点, 需要{}个主消息节点.".format(len(main_message_list), main_message_number))
    states = dict()
    for index in execute_index_sequence:
        node = message_expand_structure[index]
        if isinstance(node, SplitNode) or isinstance(node, BranchNode) or isinstance(node, SBoxNode) or isinstance(node, PNode) or isinstance(node, EqualNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
        elif isinstance(node, RotationNode) or isinstance(node, ShiftNode):
            input_state = states[node.parent_index]
            states[index] = node.pass_state(input_state)
        elif isinstance(node, MergeNode) or isinstance(node, FNode) or isinstance(node, XORNode):
            input_states_list = [states[i] for i in node.parent_index_list]
            states[index] = node.pass_state(input_states_list)
        elif isinstance(node, MessageNode):
            if index >= main_message_number:
                raise_error("正在执行消息扩展部分, 消息扩展规则不能定义MESSAGE节点!")
            states[index] = node.pass_state(main_message_list[index])
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
    message_list = [states[i] for i in message_indexes]
    return message_list

# 在执行hash_n_rounds之前先对消息进行扩展
def hash_one_block(pre_round, post_round, round_structure_list, execute_index_sequence_list, message_per_round_structure, n, message_expand_tuple, round_number, iv_bits, main_message_list):
    submessage_number = message_expand_tuple[3]
    total_message_num, message_size_per_round = message_per_round_structure
    if submessage_number is not None:
        if submessage_number != total_message_num:
            raise_error("扩展头声明的子消息字数量({})与轮函数中实际需要的数量({})不一致!".format(submessage_number, total_message_num))
    main_message_number = message_expand_tuple[4]
    message_size = message_expand_tuple[5]
    if main_message_number is not None:
        assert len(main_message_list) == main_message_number and len(main_message_list[0]) == message_size
    message_list = message_expand(message_expand_tuple, main_message_list)
    if len(message_list) != total_message_num:
        raise_error("正在计算哈希值, 用户提供的子消息数量与算法描述中消息节点总量不一致! 用户提供了{}个子消息, 算法需要{}个子消息!".format(len(message_list), total_message_num))
    # 将子消息结构化到每一轮中
    index_in_message_list = 0
    messages_per_round = dict()
    for i in ([-2] + [i for i in range(round_number)] + [-1]):
        messages_per_round[i] = []
        for message_size in message_size_per_round[i]:
            # 检查提供的子消息长度是否符合要求
            if len(message_list[index_in_message_list]) != message_size:
                raise_error("正在计算哈希值, 用户提供的第{}个子消息长度与算法描述不一致! 提供长度为{}, 算法需要子消息长度为{}!".format(index_in_message_list, len(message_list[index_in_message_list]), message_size))
            messages_per_round[i].append(message_list[index_in_message_list])
            index_in_message_list += 1
    hash_bits = iv_bits
    pre_round_states = None
    post_round_states = None
    states_per_round = []
    if pre_round:
        execute_index_sequence = sorted(pre_round)
        hash_bits, pre_round_states = hash_one_round(pre_round, hash_bits, execute_index_sequence, messages_per_round[-2], 0, (pre_round_states, states_per_round, post_round_states))
    for r in range(round_number):
        hash_bits, states = hash_one_round(round_structure_list[r], hash_bits, execute_index_sequence_list[r], messages_per_round[r], r, (pre_round_states, states_per_round, post_round_states))
        states_per_round.append(states)
    if post_round:
        execute_index_sequence = sorted(post_round)
        hash_bits, post_round_states = hash_one_round(post_round, hash_bits, execute_index_sequence, messages_per_round[-1], 0, (pre_round_states, states_per_round, post_round_states))
    return hash_bits

def get_message_per_round_structure(cipher, cipher_round_number):
    pre_round, post_round, cipher_bodys, cipher_body_loop_num = cipher[0], cipher[1], cipher[2][0], cipher[2][1]
    # 将所有循环体串联起来
    loop_num = len(cipher_body_loop_num)
    round_structure_list = []
    execute_index_sequence_list = []
    for i in range(loop_num):
        execute_sequence = sorted(cipher_bodys[i])
        for _ in range(cipher_body_loop_num[i]):
            round_structure_list.append(cipher_bodys[i])
            execute_index_sequence_list.append(execute_sequence)
    total_message_num = 0
    message_size_per_ronud = dict()
    for i in range(-2, cipher_round_number):
        message_size_per_ronud[i] = []
    if pre_round:
        for index in sorted(pre_round):
            node = pre_round[index]
            if isinstance(node, MessageNode):
                total_message_num += 1
                message_size_per_ronud[-2].append(node.size)
    # 循环体
    for i in range(cipher_round_number):
        for index in execute_index_sequence_list[i]:
            node = round_structure_list[i][index]
            if isinstance(node, MessageNode):
                total_message_num += 1
                message_size_per_ronud[i].append(node.size)
    if post_round:
        for index in sorted(post_round):
            node = post_round[index]
            if isinstance(node, MessageNode):
                total_message_num += 1
                message_size_per_ronud[-1].append(node.size)
    return (total_message_num, message_size_per_ronud), (round_structure_list, execute_index_sequence_list)
    
# 轮前和轮后都执行, 允许存在多个循环体
def hash(cipher, cipher_round_number, cipher_block_size, message_expand_tuple, n, message_block_num, given_iv_bits=None, given_main_message_lists=None):
    main_message_number = message_expand_tuple[4]
    main_message_size = message_expand_tuple[5]
    pre_round, post_round = cipher[0], cipher[1]
    message_per_round_structure, cipher_body_structure = get_message_per_round_structure(cipher, cipher_round_number)
    round_structure_list, execute_index_sequence_list = cipher_body_structure
    if given_iv_bits is None:
        iv_bits = np.frombuffer(os.urandom(cipher_block_size * n), dtype=np.uint8).reshape(cipher_block_size, n) & 1
    else:
        iv_bits = given_iv_bits
    if given_main_message_lists is None:
        main_message_lists = []
        if main_message_number is not None:
            # 用户给出了消息扩展规则, 只需要随机生成主消息节点即可
            for _ in range(message_block_num):
                main_message_lists.append(np.frombuffer(os.urandom(main_message_number * main_message_size * n), dtype=np.uint8).reshape((main_message_number, main_message_size, n)) & 1)
        else:
            # 用户没有给出消息扩展规则, 则把主消息作为每轮子消息节点并随机生成
            message_size_per_round = message_per_round_structure[1]
            for _ in range(message_block_num):
                main_message_list = []
                for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
                    for message_size in message_size_per_round[i]:
                        main_message_list.append(np.frombuffer(os.urandom(message_size * n), dtype=np.uint8).reshape(message_size, n) & 1)
                main_message_lists.append(main_message_list)
    else:
        assert len(given_main_message_lists) == message_block_num
        total_message_num = message_per_round_structure[0]
        if total_message_num > 0 and isinstance(given_main_message_lists[0][0], int):
            main_message_lists = []
            # 消息需要将转换为比特数组
            if main_message_number is None:
                message_size_per_round = message_per_round_structure[1]
                for given_main_message_list in given_main_message_lists:
                    # 用户给出的主消息列表长度必须与子消息数目一致
                    if len(given_main_message_list) != total_message_num:
                        raise_error("算法没有消息扩展结构, 用户提供的主消息节点数({})必须与算法子消息节点数之和({})一致!".format(len(given_main_message_list), total_message_num))
                    main_message_list = []
                    main_message_index = 0
                    for i in ([-2] + [i for i in range(cipher_round_number)] + [-1]):
                        for message_size in message_size_per_round[i]:
                            main_message_list.append(int_to_bits(given_main_message_list[main_message_index], message_size, False))
                            main_message_index += 1
                    main_message_lists.append(main_message_list)
            else:
                # 算法给出了消息扩展部分
                for given_main_message_list in given_main_message_lists:
                    # 用户给出的主消息列表长度必须与消息扩展部分定义一致
                    if len(given_main_message_list) != main_message_number:
                        raise_error("用户提供的主消息节点数({})必须与算法消息扩展部分定义({})一致!".format(len(given_main_message_list), main_message_number))
                    main_message_list = [int_to_bits(main_message_int, main_message_size, False) for main_message_int in given_main_message_list]
                    main_message_lists.append(main_message_list)
        else:
            # 检查
            for given_message_list in given_main_message_lists:
                if main_message_number is None:
                    assert len(given_message_list) == total_message_num
                else:
                    assert len(given_message_list) == main_message_number
            main_message_lists = given_main_message_lists
    hash_bits = iv_bits
    for main_message_list in main_message_lists:
        hash_bits = hash_one_block(pre_round, post_round, round_structure_list, execute_index_sequence_list, message_per_round_structure, n, message_expand_tuple, cipher_round_number, hash_bits, main_message_list)
    return iv_bits, main_message_lists, hash_bits