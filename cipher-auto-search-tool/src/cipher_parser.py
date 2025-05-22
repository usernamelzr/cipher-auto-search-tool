from node import *
from node_constraint import *
from util import concatenate_str_list
from error_handler import raise_node_error, raise_error

def find_whether_with_add(file_path):
    f = open(file_path, mode="r", encoding="utf-8")
    line = f.readline()
    flag = False
    find_add = False
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "cipher_dscription":
            flag = True
        elif not flag:
            line = f.readline()
            continue
        elif classified_operation_category == "operation_node":
            if operation_category == "ADD":
                find_add = True
                break
        elif classified_operation_category != "import_node":
            flag = False
        line = f.readline()
    f.close()
    return find_add

def find_large_sbox(file_path, metric=8):
    f = open(file_path, mode="r", encoding="utf-8")
    line = f.readline()
    flag = False
    find_flag = False
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        if operation_category == ".SBOX":
            find_flag = True
            input_size = int(operation[2])
            output_size = int(operation[3])
            if input_size >= metric or output_size >= metric:
                flag = True
                break
        line = f.readline()
    f.close()
    return flag, find_flag

def check_round_structure(round_structure, loop_index, search_type):
    nodes_children = dict()
    for index in round_structure:
        nodes_children[index] = []
    for index, node in round_structure.items():
        parent_index_list = get_node_parent_index_list(node)
        for parent_index in parent_index_list:
            if parent_index >= index:
                raise_node_error(index, loop_index, "父节点编号必须小于子节点编号!")
            if parent_index not in round_structure:
                raise_node_error(index, loop_index, "父节点({})不存在!".format(parent_index))
            nodes_children[parent_index].append(node)
    for index, children in nodes_children.items():
        # 除了END节点每个节点应该有出度
        out_degree = len(children)
        if out_degree == 0 and (not isinstance(round_structure[index], EndNode)):
            raise_node_error(index, loop_index, "定义的节点没有在轮函数中使用到!")
        # SPIT节点的儿子、BRANCH节点的儿子、以及PSBOX节点的儿子只算一个，如果进行线性分析，只能有一个儿子
        if search_type in ["linear", "diff_linear"]:
            split_flag = 0
            branch_flag = 0
            psbox_flag = 0
            other_children_num = 0
            for child_node in children:
                if isinstance(child_node, SplitNode):
                    split_flag = 1
                elif isinstance(child_node, BranchNode):
                    branch_flag = 1
                elif isinstance(child_node, ParallelSBoxNode):
                    psbox_flag = 1
                else:
                    other_children_num += 1
            if split_flag + branch_flag + psbox_flag + other_children_num > 1:
                raise_node_error(index, loop_index, "正在进行线性分析, 定义的节点输入到多个操作中, 子节点列表为{}, 请使用BRANCH操作将其分开!".format([child_node.index for child_node in children]))

def check_parsed_cipher(cipher_body, cipher_body_loop_num, cipher_round_number, pre_round, post_round, search_type):
    # 检查轮函数是否有内容
    if len(cipher_body) == 0:
        raise_error("缺失轮函数体结构, 或缺失.BODY标记!")

    # 检查点: 检查循环体轮数之和是否等于算法总轮数
    check_loop_sum = 0
    for num in cipher_body_loop_num:
        check_loop_sum += num
    if check_loop_sum != cipher_round_number:
        raise_error("轮函数中循环体轮数之和与算法总轮数不一致!")

    # 检查每个循环体是否合理
    check_round_structure(pre_round, -2, search_type)
    for i in range(len(cipher_body)):
        check_round_structure(cipher_body[i], i, search_type)
    check_round_structure(post_round, -1, search_type)

def classify_operation_category(operation_category):
    if operation_category[0] == "@":
        return "operation_node"
    if operation_category in ["BRANCH", "ROOT", "SPLIT", "MERGE", "XOR", "ROTATION", "SHIFT", "ADD", "SUBKEY", "MESSAGE", "END", "EQUAL", "VROTATION", "PSBOX", "CONSTANT"]:
        return "operation_node"
    if operation_category == ".CDFH":
        return "cdf_head"
    if operation_category in [".SBOX", ".P", ".F", ".CONSTANT"]:
        return "complex_operation"
    if operation_category in [".BODY", ".PREROUND", ".POSTROUND"]:
        return "cipher_description"
    if operation_category == ".LOOP":
        return "loop_head"
    if operation_category == ".EXPAND_LOOP":
        return "expand_loop_head"
    if operation_category == ".EXPAND_EQUAL":
        return "expand_equal_head"
    if operation_category == ".CONSTRAINT":
        return "constraint_head"
    if operation_category == ".MESSAGE_EXPAND":
        return "message_expand_head"
    if operation_category == ".SUBKEY_EXPAND":
        return "subkey_expand_head"
    if operation_category in ["C_CONSTANT", "C_EQUAL", "C_UNEQUALCONSTANT", "C_UNEQUAL", "C_MDIFF", "C_CONDITION", "C_CONDITIONSUM", "C_DIFFSUM"]:
        return "node_constraint"
    if operation_category == "IMPORT":
        return "import_node"
    if operation_category == "IMPORTM":
        return "import_m_node"
    if operation_category == "IMPORTK":
        return "import_key_node"
    if operation_category in ["HEAD_IMPORT", "TAIL_IMPORT"]:
        return "head_tail_import"
    if operation_category == ".OUTM":
        return "out_messages"
    if operation_category == ".OUTK":
        return "out_subkeys"
    if operation_category in ["INPUT", "OUTPUT", "ROUND", "VALUE", "EXPRESSION"]:
        return "complex_operation_definition"
    raise_error("解析到未定义的关键字: {}!".format(operation_category))

def parse_bit_index(bit_index_str, context_info):
    bit_index_strs = bit_index_str.split(",")
    bit_index = []
    for sub_bit_index in bit_index_strs:
        if "~" in sub_bit_index:
            # 一个下标范围
            bit_index_range = sub_bit_index.split("~")
            if len(bit_index_range) != 2:
                raise_error("下标范围、轮数范围、或节点列表解析错误! " + context_info)
            start_index = int(bit_index_range[0])
            end_index = int(bit_index_range[1])
            if start_index > end_index:
                raise_error("起始下标不能大于结束下标! " + context_info)
            bit_index += [i for i in range(start_index, end_index + 1)]
        else:
            bit_index.append(int(sub_bit_index))
    return bit_index

# 返回：节点列表, 节点编号列表
# 通常列表中只有一个节点，BRANCH命令返回两个节点
def parse_operation_node(operation, Sboxes, Fs, Ps, Constants):
    operation_category = operation[0]
    # 一行多节点
    if operation_category == "BRANCH":
        parent_index = int(operation[-1])
        operation_size = int(operation[-2])
        if len(operation) < 4:
            raise_error("操作语句 {} 参数太少!".format(concatenate_str_list(operation)))
        if len(operation) == 4:
            out_index_list = list(map(int, operation[1].split(",")))
        else:
            out_index_list = list(map(int, operation[1:-2]))
        res_nodes = []
        for out_index in out_index_list:
            res_nodes.append(BranchNode(out_index, operation_size, parent_index, out_index_list))
        return res_nodes, out_index_list
    if operation_category == "PSBOX":
        S_name = operation[1]
        assert S_name.startswith("@")
        S_name = S_name[1:]
        assert S_name in Sboxes
        input_length = Sboxes[S_name].input_length
        output_length = Sboxes[S_name].output_length
        output_index_list = list(map(int, operation[2].split(",")))
        operation_size = int(operation[3])
        parent_index_list = list(map(int, operation[4].split(",")))
        assert len(output_index_list) == output_length and len(parent_index_list) == input_length
        res_node_list = []
        for index in output_index_list:
            res_node = ParallelSBoxNode(index, operation_size, input_length, output_length, parent_index_list, output_index_list)
            res_node.inherit_from_SBoxNode(Sboxes[S_name])
            res_node_list.append(res_node)
        return res_node_list, output_index_list
    # 一行一节点
    if operation_category == "ROOT":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        res_node = RootNode(operation_index, operation_size)
    elif operation_category == "SPLIT":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index = int(operation[3])
        bit_index = parse_bit_index(operation[4], "正在解析语句 {}.".format(concatenate_str_list(operation)))
        if operation_size != len(bit_index):
            raise_error("正在解析语句 {}, SPLIT节点定义中状态大小与下标范围冲突!".format(concatenate_str_list(operation)))
        res_node = SplitNode(operation_index, operation_size, bit_index, parent_index)
    elif operation_category == "MERGE":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        if len(operation) < 4:
            raise_error("操作语句 {} 参数太少!".format(concatenate_str_list(operation)))
        if len(operation) == 4:
            parent_index_list = list(map(int, operation[3].split(",")))
        else:
            parent_index_list = list(map(int, operation[3:]))
        res_node = MergeNode(operation_index, operation_size, parent_index_list)
    elif operation_category == "XOR":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        if len(operation) < 4:
            raise_error("操作语句 {} 参数太少!".format(concatenate_str_list(operation)))
        if len(operation) == 4:
            parent_index_list = list(map(int, operation[3].split(",")))
        else:
            parent_index_list = list(map(int, operation[3:]))
        res_node = XORNode(operation_index, operation_size, parent_index_list)
    elif operation_category == "ROTATION":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index = int(operation[3])
        if operation[4][0] == "@":
            # 移位数为轮常数
            is_variable = True
            C_name = operation[4][1:]
            if C_name not in Constants:
                raise_error("用户未定义的轮常数名称! 正在解析语句 " + concatenate_str_list(operation) + ".")
            left_shift_number = Constants[C_name].constant
        else:
            # 移位数为字面量
            is_variable = False
            left_shift_number = int(operation[4])
        res_node = RotationNode(operation_index, operation_size, parent_index, left_shift_number, is_variable)
    elif operation_category == "SHIFT":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index = int(operation[3])
        if operation[4][0] == "@":
            # 移位数为轮常数
            is_variable = True
            C_name = operation[4][1:]
            if C_name not in Constants:
                raise_error("用户未定义的轮常数名称! 正在解析语句 " + concatenate_str_list(operation) + ".")
            left_shift_number = Constants[C_name].constant
        else:
            # 移位数为字面量
            is_variable = False
            left_shift_number = int(operation[4])
        left_shift_number = int(operation[4])
        res_node = ShiftNode(operation_index, operation_size, parent_index, left_shift_number, is_variable)
    elif operation_category == "ADD":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index1 = int(operation[3])
        parent_index2 = int(operation[4])
        res_node = AddNode(operation_index, operation_size, parent_index1, parent_index2)
    elif operation_category == "SUBKEY":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        res_node = SubKeyNode(operation_index, operation_size)
    elif operation_category == "MESSAGE":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        res_node = MessageNode(operation_index, operation_size)
    elif operation_category == "EQUAL":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index = int(operation[3])
        res_node = EqualNode(operation_index, operation_size, parent_index)
    elif operation_category == "VROTATION":
        rotation_category = operation[1]
        if rotation_category == "R" or rotation_category == "r":
            rotation_category = "r"
        else:
            rotation_category = "l"
        operation_index = int(operation[2])
        operation_size = int(operation[3])
        case_index=int(operation[4])
        case_size=int(operation[5])
        parent_index =int(operation[6])
        res_node = VarRotationNode(operation_index, operation_size, case_size, case_index, parent_index, rotation_category)
    elif operation_category == "END":
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        parent_index = int(operation[3])
        res_node = EndNode(operation_index, operation_size, parent_index)
    elif operation_category == "CONSTANT":
        # 不随轮次改变的常数节点
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        constant = int(operation[3], base=0)
        res_node = ConstantNode(operation_index, operation_size, constant, False)
    elif operation_category[0] == "@":
        operation_name = operation_category[1:]
        operation_index = int(operation[1])
        operation_size = int(operation[2])
        if operation_name in Sboxes:
            parent_index = int(operation[3])
            res_node = copy.deepcopy(Sboxes[operation_name])
            res_node.index = operation_index
            res_node.parent_index = parent_index
        elif operation_name in Ps:
            parent_index = int(operation[3])
            res_node = copy.deepcopy(Ps[operation_name])
            res_node.index = operation_index
            res_node.parent_index = parent_index
        elif operation_name in Fs:
            res_node = copy.deepcopy(Fs[operation_name])
            res_node.index = operation_index
            if len(operation) < 4:
                raise_error("操作语句 {} 参数太少!".format(concatenate_str_list(operation)))
            if len(operation) == 4:
                res_node.parent_index_list = list(map(int, operation[3].split(",")))
            else:
                res_node.parent_index_list = list(map(int, operation[3:]))
        elif operation_name in Constants:
            res_node = copy.deepcopy(Constants[operation_name])
            res_node.index = operation_index
        else:
            raise_error("自定义操作或轮常数{}找不到定义!".format(operation_name))
        if operation_size != res_node.size:
            raise_error("定义节点大小与用户自定义{}不符! 正在解析语句 {}.".format(operation_category, concatenate_str_list(operation)))
    return [res_node], [operation_index]

# 解析用户自定义的复杂操作
# 返回用户自定义操作字典, 返回值:
# Sboxes: 自定义S盒
# Fs: 自定义F函数
# Ps: 自定义P置换
# Constants: 自定义轮常数
def parse_complex_operation(file_path, search_type="diff", whether_consider_pr=True):
    assert search_type in ["diff", "linear", "diff_linear", "real", "diff_real", "other"]
    f = open(file_path, mode="r", encoding="utf-8")
    Fs = dict()
    Sboxes = dict()
    Ps = dict()
    Constants = dict()
    line = f.readline()
    while line:
        line = line.split()
        if not line:
            line = f.readline()
            continue
        operation_category = line[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        if classify_operation_category(operation_category) != "complex_operation":
            line = f.readline()
            continue
        if operation_category == ".SBOX":
            Sbox_name = line[1]
            input_size = int(line[2])
            output_size = int(line[3])
            input_values = f.readline().split()
            if input_values[0] != "INPUT":
                raise_error("S盒定义的输入请以关键字INPUT开头!")
            output_values = f.readline().split()
            if output_values[0] != "OUTPUT":
                raise_error("S盒定义的输出请以关键字OUTPUT开头!")
            input_values = input_values[1:]
            output_values = output_values[1:]
            if len(input_values) != 2**input_size or len(output_values) != 2**input_size:
                raise_error("正在解析S盒{}定义, 查找表长度与S盒输入长度不符!".format(Sbox_name))
            sbox_lookup_table = [-1] * (2**input_size)
            for i in range(len(input_values)):
                input_val = int(input_values[i], base=0)
                output_val = int(output_values[i], base=0)
                if sbox_lookup_table[input_val] != -1:
                    raise_error("正在解析S盒{}定义, S盒输入值重定义!".format(Sbox_name))
                sbox_lookup_table[input_val] = output_val
            Sbox = SBoxNode(0, input_size, output_size, sbox_lookup_table, 0)
            if search_type == "diff" or search_type == "diff_linear":
                Sbox.build_sbox_clauses("diff", whether_consider_pr)
            if search_type == "linear" or search_type == "diff_linear":
                Sbox.build_sbox_clauses("linear", whether_consider_pr)
            if search_type == "real":
                Sbox.build_sbox_clauses("real", False)
            if search_type == "diff_real":
                Sbox.build_sbox_clauses("diff_real", False)
            Sboxes[Sbox_name] = Sbox
        elif operation_category == ".F":
            function_name = line[1]
            size = int(line[2])
            var_num = int(line[3])
            expression_str = f.readline().strip()
            if not expression_str.startswith("EXPRESSION"):
                raise_error("F函数定义的表达式请以关键字EXPRESSION开头!")
            expression_str = expression_str[len("EXPRESSION"):].strip()
            tmp_F = FNode(0, size, [], var_num, expression_str)
            if search_type == "diff" or search_type == "diff_linear":
                tmp_F.build_function_clauses("diff")
            if search_type == "linear" or search_type == "diff_linear":
                tmp_F.build_function_clauses("linear")
            if search_type == "diff_real":
                tmp_F.build_function_clauses_diff_real()
            Fs[function_name] = tmp_F
        elif operation_category == ".P":
            P_name = line[1]
            input_size = int(line[2])
            output_size = int(line[3])
            input_values = f.readline().split()
            output_values = f.readline().split()
            if input_values[0] != "INPUT":
                raise_error("P置换定义的输入请以关键字INPUT开头!")
            if output_values[0] != "OUTPUT":
                raise_error("P置换定义的输出请以关键字OUTPUT开头!")
            input_values = input_values[1:]
            output_values = output_values[1:]
            if len(input_values) != output_size or len(output_values) != output_size:
                raise_error("正在解析P置换{}定义, 置换表长度与P置换输入长度不符!".format(P_name))
            p_bit_out_to_in = [-1] * output_size
            for i in range(len(output_values)):
                input_val = int(input_values[i], base=0)
                output_val = int(output_values[i], base=0)
                if p_bit_out_to_in[output_val] != -1:
                    raise_error("正在解析P置换{}定义, 置换表存在重定义!".format(P_name))
                p_bit_out_to_in[output_val] = input_val
            Ps[P_name] = PNode(0, 0, input_size, output_size, p_bit_out_to_in)
        elif operation_category == ".CONSTANT":
            C_name = line[1]
            constant_size = int(line[2])
            round_index_list = f.readline().split()
            constant_list_str = f.readline().split()
            if round_index_list[0] != "ROUND":
                raise_error("轮常数定义中轮次范围请以关键字ROUND开头")
            if constant_list_str[0] != "VALUE":
                raise_error("轮常数定义中常数取值请以关键字VALUE开头")
            round_index_list = round_index_list[1:]
            constant_list_str = constant_list_str[1:]
            constant_list = [int(i, base=0) for i in constant_list_str]
            # 轮数和取值一一对应
            if len(round_index_list) != len(constant_list):
                raise_error("正在解析用户自定义轮常数{}, 轮数范围与常数取值数量不一致!".format(C_name))
            constant_per_round = dict()
            for i in range(len(round_index_list)):
                for round_index in parse_bit_index(round_index_list[i], "正在解析用户自定义轮常数{}.".format(C_name)):
                    constant_per_round[round_index] = constant_list[i]
            Constants[C_name] = ConstantNode(0, constant_size, constant_per_round, True)
        line = f.readline()
    f.close()
    return Sboxes, Fs, Ps, Constants

# 解析算法描述部分
def parse_cipher_body(file_path, Sboxes, Fs, Ps, Constants):
    f = open(file_path, mode="r", encoding="utf-8")
    # 轮函数循环体列表以及每个循环体轮数
    cipher_body = []
    cipher_body_loop_num = []
    # 轮函数前操作和轮函数后操作
    pre_round = dict()
    post_round = dict()
    line = f.readline()
    # environment_flag取值：-3, 非算法描述环境；-2, 轮函数前操作；-1, 轮函数后操作；0~, 轮函数循环体
    environment_flag = -3
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "cdf_head":
            cipher_category = "block"
            if operation[1] == "HASH":
                cipher_category = "hash"
            cipher_round_number = int(operation[-2])
            cipher_block_size = int(operation[-1])
        elif classified_operation_category == "loop_head":
            if environment_flag < 0:
                raise_error("缺失.BODY标记, 或循环体没有定义在.BODY中!")
            if len(cipher_body) > 0:
                environment_flag += 1
            cipher_body.append(dict())
            cipher_body_loop_num.append(int(operation[1]))
        elif classified_operation_category == "cipher_description":
            if operation_category == ".BODY":
                if environment_flag >= 0:
                    raise_error("轮函数体.BODY重定义!")
                environment_flag = 0
            elif operation_category == ".PREROUND":
                environment_flag = -2
            elif operation_category == ".POSTROUND":
                environment_flag = -1
        elif environment_flag == -3:
            line = f.readline()
            continue
        elif classified_operation_category == "operation_node" or classified_operation_category == "import_node":
            if environment_flag == -2:
                target_dict = pre_round
            elif environment_flag == -1:
                target_dict = post_round
            else:
                if environment_flag == 0 and len(cipher_body) == 0:
                    # 用户并没有提供.LOOP关键字
                    cipher_body.append(dict())
                    cipher_body_loop_num.append(cipher_round_number)
                target_dict = cipher_body[environment_flag]
            if classified_operation_category == "operation_node":
                nodes, indexes = parse_operation_node(operation, Sboxes, Fs, Ps, Constants)
                for i in range(len(nodes)):
                    if indexes[i] in target_dict:
                        raise_node_error(indexes[i], environment_flag, "节点编号重复定义!")
                    if isinstance(nodes[i], RootNode) and nodes[i].size != cipher_block_size:
                        raise_node_error(indexes[i], environment_flag, "ROOT节点状态大小必须等于算法分组大小! ROOT节点解析到为{}比特, .CDFH算法头解析到分组大小为{}比特!".format(nodes[i].size, cipher_block_size))
                    target_dict[indexes[i]] = nodes[i]
            else:
                operation_index = int(operation[1])
                if operation_index in target_dict:
                    raise_node_error(indexes[i], environment_flag, "节点编号重复定义!")
                operation_size = int(operation[2])
                if environment_flag == -2:
                    raise_error("轮前结构不允许引用! 引用节点编号:{}!".format(operation_index))
                target_info = operation[3].strip("()").split(",")
                if len(target_info) != 2:
                    raise_error("算法结构中IMPORT节点解析错误, 节点编号为{}!".format(operation_index))
                round_index = target_info[0]
                if round_index.isdigit():
                    # 绝对轮数
                    round_index = int(round_index)
                elif round_index == "pre-round":
                    round_index = -2
                elif round_index == "post-round":
                    raise_error("算法结构中引用不允许引用轮后节点! 引用节点编号: {}, 引用信息: {}!".format(operation_index, operation[3]))
                elif round_index.startswith("r-"):
                    if environment_flag == -1:
                        raise_error("轮后结构不允许使用相对引用的格式! 轮数r未定义!")
                    round_index = -2 + int(round_index[1:])
                elif round_index.startswith("-"):
                    if environment_flag == -1:
                        raise_error("轮后结构不允许使用相对引用的格式! 轮数r未定义!")
                    round_index = -2 + int(round_index)
                else:
                    raise_error("算法结构中引用信息错误! 引用节点编号: {}, 引用信息: {}!".format(operation_index, operation[3]))
                if not target_info[1].isdigit():
                    raise_error("算法结构中引用信息错误! 引用节点编号: {}, 引用信息: {}!".format(operation_index, operation[3]))
                index_in_round = int(target_info[1])
                target_dict[operation_index] = ImportNode(operation_index, operation_size, round_index, index_in_round)
        else:
            environment_flag = -3
        line = f.readline()
    f.close()
    return cipher_category, cipher_round_number, cipher_block_size, pre_round, post_round, cipher_body, cipher_body_loop_num

def parse_cipher_constraint(file_path, Sboxes, Fs, Ps, Constants):
    f = open(file_path, mode="r", encoding="utf-8")
    constraint_nodes = dict()
    constraints = []
    line = f.readline()
    constraint_flag = False
    with_cond_flag = False
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "constraint_head":
            if constraint_flag:
                raise_error("约束标记.CONSTRAINT重定义")
            constraint_flag = True
        elif not constraint_flag:
            line = f.readline()
            continue
        # 约束部分的操作节点
        elif classified_operation_category == "import_node":
            node_index = int(operation[1])
            node_size = int(operation[2])
            target_info = operation[3].strip("()").split(",")
            if node_index in constraint_nodes:
                raise_error("约束部分节点编号{}重复定义!".format(node_index))
            if len(target_info) != 2:
                raise_error("约束部分IMPORT节点解析错误, 节点编号为{}!".format(node_index))
            round_index = target_info[0]
            if round_index.isdigit():
                round_index = int(round_index)
            else:
                if round_index not in ["pre-round", "post-round"]:
                    raise_error("约束部分IMPORT节点引用轮次{}无法解析, 节点编号为{}!".format(round_index, node_index))
                if round_index == "pre-round":
                    round_index = -2
                else:
                    round_index = -1
            index_in_round = int(target_info[1])
            constraint_nodes[node_index] = ImportNode(node_index, node_size, round_index, index_in_round)
        elif classified_operation_category == "head_tail_import":
            node_index = int(operation[1])
            node_size = int(operation[2])
            index_in_round = int(operation[3])
            if node_index in constraint_nodes:
                raise_error("约束部分节点编号{}重复定义!".format(node_index))
            constraint_nodes[node_index] = HeadImportNode(node_index, node_size, index_in_round) if operation_category == "HEAD_IMPORT" else TailImportNode(node_index, node_size, index_in_round)
        elif classified_operation_category == "operation_node":
            nodes, indexes = parse_operation_node(operation, Sboxes, Fs, Ps, Constants)
            for i in range(len(nodes)):
                if indexes[i] in constraint_nodes:
                    raise_error("约束部分节点编号{}重复定义!".format(indexes[i]))
                constraint_nodes[indexes[i]] = nodes[i]
        elif classified_operation_category == "node_constraint":
            if operation_category == "C_CONSTANT":
                if operation[1] == "DIFF":
                    constraint_category = "diff"
                elif operation[1] == "REAL":
                    constraint_category = "real"
                elif operation[1] == "LINEAR":
                    constraint_category = "linear"
                else:
                    # 默认是对差分进行约束
                    constraint_category = "diff"
                constant_value = int(operation[-1], base=0)
                target_node_index = int(operation[-3])
                bit_index = parse_bit_index(operation[-2], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                constraints.append(ConstantConstraint(target_node_index, bit_index, constant_value, constraint_category))
            elif operation_category == "C_UNEQUALCONSTANT":
                constraint_category = "diff"
                if operation[1] == "REAL":
                    constraint_category = "real"
                constant_value = int(operation[-1], base=0)
                target_node_index = int(operation[-3])
                bit_index = parse_bit_index(operation[-2], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                constraints.append(UnequalConstantConstraint(target_node_index, bit_index, constant_value, constraint_category))
            elif operation_category == "C_EQUAL":
                constraint_category = "diff"
                if operation[1] == "REAL":
                    constraint_category = "real"
                target_node_index_1 = int(operation[-3])
                target_node_index_2 = int(operation[-2])
                bit_index = parse_bit_index(operation[-1], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                constraints.append(EqualConstraint(target_node_index_1, target_node_index_2, bit_index, constraint_category))
            elif operation_category == "C_UNEQUAL":
                constraint_category = "diff"
                if operation[1] == "REAL":
                    constraint_category = "real"
                target_node_index_1 = int(operation[-3])
                target_node_index_2 = int(operation[-2])
                bit_index = parse_bit_index(operation[-1], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                constraints.append(UnequalConstraint(target_node_index_1, target_node_index_2, bit_index, constraint_category))
            elif operation_category == "C_MDIFF":
                target_node_index = int(operation[1])
                bit_index = parse_bit_index(operation[2], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                diff_constant = int(operation[3], base=0)
                real_constant = int(operation[4], base=0)
                constraints.append(MdiffConstraint(target_node_index, bit_index, diff_constant, real_constant))
            elif operation_category == "C_CONDITION":
                target_node_index = int(operation[1])
                fore_node_index = int(operation[2])
                bit_index = parse_bit_index(operation[3], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                conditions = operation[4]
                constraints.append(ConditionConstraint(target_node_index, fore_node_index, bit_index, conditions))
            elif operation_category == "C_CONDITIONSUM":
                # 解析到限制条件数的语句就为每个节点增加条件变量
                with_cond_flag = True
                target_node_indexes = parse_bit_index(operation[1], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                max_cond_sum = int(operation[2])
                constraints.append(ConditionSumConstraint(target_node_indexes, max_cond_sum))
            elif operation_category == "C_DIFFSUM":
                # 解析到限制差分比特数的语句
                target_node_indexes = parse_bit_index(operation[1], "正在解析约束 {}.".format(concatenate_str_list(operation)))
                max_diff_sum = int(operation[2])
                constraints.append(DiffSumConstraint(target_node_indexes, max_diff_sum))
        else:
            break
        line = f.readline()
    f.close()
    return constraint_nodes, constraints, with_cond_flag

def parse_message_expand_table(f, cipher_category, message_nodes, main_message_number, Sboxes, Fs, Ps, Constants):
    message_indexes = []
    line = f.readline()
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "operation_node":
            nodes, indexes = parse_operation_node(operation, Sboxes, Fs, Ps, Constants)
            for i in range(len(nodes)):
                if indexes[i] < main_message_number:
                    raise_error("消息(密钥)扩展规则中正在解析第{}个节点, 前{}个编号的节点默认为主消息(主密钥)!".format(indexes[i], main_message_number))
                if indexes[i] in message_nodes:
                    raise_error("消息(密钥)扩展部分中正在解析第{}个节点, 节点编号重定义!".format(indexes[i]))
                message_nodes[indexes[i]] = nodes[i]
        elif classified_operation_category == "out_messages" or classified_operation_category == "out_subkeys":
            message_indexes = list(map(int, operation[1:]))
        else:
            break
        line = f.readline()
    return message_indexes

def parse_message_expand_iter(f, cipher_category, message_nodes, main_message_number, Sboxes, Fs, Ps, Constants):
    message_index_ranges = []
    message_expand_structures = []
    flag = False
    line = f.readline()
    output_indexes = []
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "expand_loop_head":
            if len(operation) != 2:
                raise_error("正在解析语句 {}, .EXPAND_LOOP后的编号范围请不要有空格!".format(concatenate_str_list(operation)))
            message_index_ranges.append(parse_bit_index(operation[1], "正在解析语句 {}!".format(concatenate_str_list(operation))))
            message_expand_structures.append(dict())
            flag = True
        elif classified_operation_category == "expand_equal_head":
            sub_message_indexes = parse_bit_index(operation[1], "正在解析: {}".format(line))
            main_message_indexes = parse_bit_index(operation[2], "正在解析: {}".format(line))
            assert len(sub_message_indexes) == len(main_message_indexes)
            if len(sub_message_indexes) != len(main_message_indexes):
                if cipher_category == "block":
                    raise_error("正在解析语句 {}, 子密钥与主密钥编号数量不一致!".format(concatenate_str_list(operation)))
                else:
                    raise_error("正在解析语句 {}, 子消息与主消息编号数量不一致!".format(concatenate_str_list(operation)))
            for i in range(len(sub_message_indexes)):
                message_index_ranges.append([sub_message_indexes[i]])
                tmp_structure = dict()
                tmp_structure[0] = ImportMNode(0, message_nodes[main_message_indexes[i]].size, str(main_message_indexes[i]), True)
                tmp_structure[1] = EndNode(1, tmp_structure[0].size, 0)
                message_expand_structures.append(tmp_structure)
            flag = False
        elif classified_operation_category == "import_m_node" or classified_operation_category == "import_key_node":
            if not flag:
                raise_error("必须先声明一个迭代头.EXPANDLOOP 起始子消息(密钥)编号 结束子消息(密钥)编号, 再写迭代结构!")
            if classified_operation_category == "import_m_node" and cipher_category == "block":
                raise_error("分组密码中请使用IMPORTK语句引用密钥, 不要使用IMPORTM!")
            if classified_operation_category == "import_key_node" and cipher_category == "hash":
                raise_error("哈希算法中请使用IMPORTM语句引用消息, 不要使用IMPORTK!")
            operation_index = int(operation[1])
            operation_size = int(operation[2])
            target_info = operation[3]
            if target_info.startswith("r-"):
                # 引用前面轮的子消息
                target_index = target_info[2:]
                is_main_message = False
            elif target_info.startswith("-"):
                # 引用前面轮的子消息
                target_index = target_info[1:]
                is_main_message = False
            elif target_info.startswith("m"):
                # 引用主消息
                target_index = target_info[1:]
                is_main_message = True
            else:
                if cipher_category == "hash":
                    raise_error("编号为{}的IMPORTM节点引用格式错误!".format(operation_index))
                else:
                    raise_error("编号为{}的IMPORTK节点引用格式错误!".format(operation_index))
            message_expand_structures[-1][operation_index] = ImportMNode(operation_index, operation_size, target_index, is_main_message)
        elif classified_operation_category == "operation_node":
            if not flag:
                raise_error("必须先声明一个迭代头.EXPANDLOOP 起始子消息(密钥)编号 结束子消息(密钥)编号, 再写迭代结构!")
            nodes, indexes = parse_operation_node(operation, Sboxes, Fs, Ps, Constants)
            for i in range(len(nodes)):
                if indexes[i] in message_expand_structures[-1]:
                    raise_error("消息扩展部分中正在解析第{}个节点, 节点编号重定义!".format(indexes[i]))
                message_expand_structures[-1][indexes[i]] = nodes[i]
        elif classified_operation_category == "import_node":
            operation_index = int(operation[1])
            operation_size = int(operation[2])
            if operation_index in message_expand_structures[-1]:
                raise_error("IMPORT语句{}, 节点编号{}重定义!".format(concatenate_str_list(operation), operation_index))
            target_info = operation[3].strip("()").split(",")
            if len(target_info) != 2:
                    raise_error("EXPAND_LOOP中IMPORT节点解析错误, 语句为{}!".format(concatenate_str_list(operation)))
            round_index = target_info[0]
            index_in_round = target_info[1]
            if not index_in_round.isdigit():
                raise_error("语句{}, 引用节点编号格式错误!".format(concatenate_str_list(operation)))
            index_in_round = int(index_in_round)
            if round_index.isdigit():
                # 绝对轮数
                round_index = int(round_index)
            elif round_index.startswith("r-"):
                round_index = round_index[2:]
                if round_index.startswith("@"):
                    C_name = round_index[1:]
                    if C_name not in Constants:
                        raise_error("语句{}引用了未定义的轮常数{}!".format(concatenate_str_list(operation), C_name))
                    round_index = C_name
                else:
                    round_index = -2 - int(round_index)
            elif round_index.startswith("-"):
                round_index = round_index[1:]
                if round_index.startswith("@"):
                    C_name = round_index[1:]
                    if C_name not in Constants:
                        raise_error("语句{}引用了未定义的轮常数{}!".format(concatenate_str_list(operation), C_name))
                    round_index = C_name
                else:
                    round_index = -2 - int(round_index)
            elif round_index in ["pre-round", "post-round"]:
                raise_error("语句{}, 不在轮函数中，不允许引用轮函数节点!".format(concatenate_str_list(operation)))
            else:
                raise_error("语句{}, 引用格式错误!".format(concatenate_str_list(operation)))
            message_expand_structures[-1][operation_index] = ImportNode(operation_index, operation_size, round_index, index_in_round)
        elif classified_operation_category == "out_messages" or classified_operation_category == "out_subkeys":
            if cipher_category == "block" and classified_operation_category == "out_messages":
                raise_error("使用了.OUTM, 在分组密码中请使用.OUTK!")
            if cipher_category == "hash" and classified_operation_category == "out_subkeys":
                raise_error("使用了.OUTK, 在哈希算法中请使用.OUTM!")
            output_indexes = list(map(int, operation[1:]))
        else:
            break
        line = f.readline()
    index_in_message_nodes = main_message_number
    max_message_index = -1
    message_index_to_structure = dict()
    message_indexes = []
    global_in_to_out = dict()
    for i in range(len(message_index_ranges)):
        for j in message_index_ranges[i]:
            if j in message_index_to_structure:
                raise_error("正在解析消息(密钥)扩展部分, 各个子消息(密钥)范围有重叠!")
            message_index_to_structure[j] = message_expand_structures[i]
            if j > max_message_index:
                max_message_index = j
    for i in range(max_message_index + 1):
        in_to_out = dict()
        if not i in message_index_to_structure:
            raise_error("正在解析消息(密钥)扩展部分, 第{}个子消息(密钥)无定义!".format(i))
        execute_sequence = sorted(message_index_to_structure[i])
        for j in execute_sequence:
            in_to_out[j] = index_in_message_nodes
            global_in_to_out[(i,j)] = index_in_message_nodes
            index_in_message_nodes += 1
        for j in execute_sequence:
            node = message_index_to_structure[i][j]
            if isinstance(node, ImportMNode):
                target_info = node.target_message_index
                if target_info.startswith("@"):
                    C_name = target_info[1:]
                    if C_name not in Constants:
                        if cipher_category == "hash":
                            raise_error("IMPORTM引用的主消息编号变量{}无定义!".format(C_name))
                        else:
                            raise_error("IMPORTK引用的主密钥编号变量{}无定义!".format(C_name))
                    target_index = Constants[C_name].get_constant(i)
                else:
                    target_index = int(target_info)
                # 用EqualNode代替
                if node.is_main_message:
                    if target_index >= main_message_number:
                        if cipher_category == "hash":
                            raise_error("主消息编号{}超出范围, 只有{}个主消息字!".format(target_index, main_message_number))
                        else:
                            raise_error("主密钥编号{}超出范围, 只有{}个主密钥字!".format(target_index, main_message_number))
                    new_node = EqualNode(in_to_out[j], node.size, target_index)
                else:
                    if target_index == 0:
                        if cipher_category == "hash":
                            raise_error("IMPORTM操作不能通过IMPORTM r-0引用自己!")
                        else:
                            raise_error("IMPORTK操作不能通过IMPORTK r-0引用自己!")
                    target_index = i - target_index
                    if target_index < 0:
                        if cipher_category == "hash":
                            raise_error("IMPORTM节点引用了第{}的子消息节点, 其不存在!".format(target_index))
                        else:
                            raise_error("IMPORTK节点引用了第{}个子密钥节点, 其不存在!".format(target_index))
                    new_node = EqualNode(in_to_out[j], node.size, message_indexes[target_index])
            elif isinstance(node, ImportNode):
                target_info = node.round_index
                if isinstance(target_info, str):
                    target_info = i - Constants[target_info].get_constant(i)
                elif target_info < 0:
                    target_info = i + 2 + target_info
                if target_info < 0 or target_info >= i:
                    raise_error("正在生成第{}个子消息(密钥)字, 引用了第{}个子消息(密钥)字相关的节点!".format(i, target_info))
                new_node = EqualNode(in_to_out[j], node.size, global_in_to_out[(target_info, node.index_in_round)])
            else:
                new_node = copy.copy(node)
                new_node.index = in_to_out[j]
                # 需要改变常数的量
                if isinstance(new_node, ConstantNode) and new_node.is_variable:
                    new_node = ConstantNode(new_node.index, new_node.size, new_node.constant[i], False)
                # 需要改变父亲节点
                if isinstance(new_node, BranchNode) or isinstance(new_node, SplitNode) or isinstance(new_node, RotationNode) or isinstance(new_node, ShiftNode) or isinstance(new_node, EqualNode) or isinstance(new_node, SBoxNode) or isinstance(new_node, PNode):
                    new_node.parent_index = in_to_out[new_node.parent_index]
                # 对于RotationNode和ShiftNode，特判是否为可变常数
                elif isinstance(new_node, RotationNode) or isinstance(new_node, ShiftNode):
                    new_node.parent_index = in_to_out[new_node.parent_index]
                    if new_node.is_variable:
                        parsed_constant = new_node.left_shift_number[i]
                        new_node.is_variable = False
                        new_node.left_shift_number = parsed_constant
                elif isinstance(new_node, ParallelSBoxNode):
                    new_node.parent_index_list = [in_to_out[parent_index] for parent_index in new_node.parent_index_list]
                    new_node.output_index_list = [in_to_out[output_index] for output_index in new_node.output_index_list]
                elif isinstance(new_node, MergeNode) or isinstance(new_node, FNode) or isinstance(new_node, XORNode):
                    new_node.parent_index_list = [in_to_out[parent_index] for parent_index in new_node.parent_index_list]
                elif isinstance(new_node, AddNode):
                    new_node.parent_index1 = in_to_out[new_node.parent_index1]
                    new_node.parent_index2 = in_to_out[new_node.parent_index2]
                elif isinstance(new_node, EndNode):
                    new_node.parent_index = in_to_out[new_node.parent_index]
                    message_indexes.append(new_node.index)
                    # 把EndNode换成EqualNode
                    new_node = EqualNode(new_node.index, new_node.size, new_node.parent_index)
                    message_nodes[new_node.index] = new_node
                elif isinstance(new_node,VarRotationNode):
                    new_node.parent_index = in_to_out[new_node.parent_index]
                    new_node.case_index = in_to_out[new_node.case_index]
            message_nodes[new_node.index] = new_node
        if len(message_indexes) != i + 1:
            raise_error("存在没有END节点的.EXPANDLOOP结构!")
    if output_indexes:
        message_indexes = [message_indexes[i] for i in output_indexes]
    return message_indexes

def parse_expand_schedule(file_path, cipher_category, Sboxes, Fs, Ps, Constants):
    f = open(file_path, mode="r", encoding="utf-8")
    message_nodes = dict()
    expand_method = None
    sub_message_number = None
    main_message_number = None
    main_message_size = None
    line = f.readline()
    while line:
        operation = line.split()
        if not operation:
            line = f.readline()
            continue
        operation_category = operation[0]
        if operation_category.startswith("//") or operation_category.startswith("#"):
            line = f.readline()
            continue
        classified_operation_category = classify_operation_category(operation_category)
        if classified_operation_category == "message_expand_head" or classified_operation_category == "subkey_expand_head":
            if classified_operation_category == "message_expand_head" and cipher_category == "block":
                raise_error("分组密码中无法定义消息扩展!")
            if classified_operation_category == "subkey_expand_head" and cipher_category == "hash":
                raise_error("哈希算法中无法定义密钥扩展!")
            # 先找到消息扩展头
            expand_method = operation[1]
            if expand_method not in ["ITER", "TABLE"]:
                raise_error("正在解析扩展规则, 扩展方式只能是迭代式(ITER)或者打表式(TABLE)! 解析到的扩展方式为{}.".format(expand_method))
            sub_message_number = int(operation[2])
            main_message_number = int(operation[3])
            main_message_size = int(operation[4])
            # 主消息必须为前main_message_number个节点
            if cipher_category == "hash":
                for node_index in range(main_message_number):
                    node = MessageNode(node_index, main_message_size)
                    message_nodes[node_index] = node
            else:
                for node_index in range(main_message_number):
                    node = SubKeyNode(node_index, main_message_size)
                    message_nodes[node_index] = node
            break
        line = f.readline()
    if main_message_number is None:
        # 没有解析到扩展规则
        return message_nodes, [], "", sub_message_number, main_message_number, main_message_size
    if expand_method == "TABLE":
        message_indexes = parse_message_expand_table(f, cipher_category, message_nodes, main_message_number, Sboxes, Fs, Ps, Constants)
    else:
        message_indexes = parse_message_expand_iter(f, cipher_category, message_nodes, main_message_number, Sboxes, Fs, Ps, Constants)
    if len(message_indexes) != sub_message_number:
        raise_error("正在解析子消息(密钥)扩展规则, 产生的子消息(密钥)字数量({})与扩展头声明({})不一致!".format(len(message_indexes), sub_message_number))
    f.close()
    return message_nodes, message_indexes, expand_method, sub_message_number, main_message_number, main_message_size

# 支持的搜索模型search_type包括: "diff", 差分搜索; "linear", 线性搜索; "diff_linear", 差分线性搜索; "real", 真实值搜索（用于不可能差分）; "diff_real", 差分+真实值搜索（用于hash搜索）
# 返回:
# cipher_round_number: 算法总轮数
# cipher_block_size: 算法状态大小
# cipher: pre_round, 轮函数前结构；post_round, 轮函数后结构；cipher_body, 轮函数循环体列表
# constraint_nodes: 约束部分的节点
# constraints: 约束部分的约束条件
def parse_cipher_description_file(file_path, search_type, whether_consider_pr):
    Sboxes, Fs, Ps, Constants = parse_complex_operation(file_path, search_type, whether_consider_pr)
    constraint_nodes, constraints, with_cond_flag = parse_cipher_constraint(file_path, Sboxes, Fs, Ps, Constants)
    cipher_category, cipher_round_number, cipher_block_size, pre_round, post_round, cipher_body, cipher_body_loop_num = parse_cipher_body(file_path, Sboxes, Fs, Ps, Constants)
    message_expand_info = parse_expand_schedule(file_path, cipher_category, Sboxes, Fs, Ps, Constants)
    check_parsed_cipher(cipher_body, cipher_body_loop_num, cipher_round_number, pre_round, post_round, search_type)
    return (cipher_category, cipher_round_number, cipher_block_size), (pre_round, post_round, (cipher_body, cipher_body_loop_num)), (constraint_nodes, constraints, with_cond_flag), message_expand_info