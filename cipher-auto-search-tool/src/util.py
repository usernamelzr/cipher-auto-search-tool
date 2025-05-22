import numpy as np

assess_cmd = "./bin/assess"

def random_res_path(cipher_name):
    return "./search_res/" + cipher_name + "_randomtest_res.txt"

class LogicalOperationNode(object):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def visit(self, vars_values):
        pass

class VarOperationNode(LogicalOperationNode):
    def __init__(self, child1, child2, var_name):
        super().__init__(child1, child2)
        self.var_name = var_name
    
    def visit(self, vars_values):
        return vars_values[self.var_name]
    
class NotOperationNode(LogicalOperationNode):
    def __init__(self, child1, child2):
        super().__init__(child1, child2)
    
    def visit(self, vars_values):
        return ~self.child1.visit(vars_values)
    
class OrOperationNode(LogicalOperationNode):
    def __init__(self, child1, child2):
        super().__init__(child1, child2)

    def visit(self, vars_values):
        return self.child1.visit(vars_values) | self.child2.visit(vars_values)
    
class AndOperationNode(LogicalOperationNode):
    def __init__(self, child1, child2):
        super().__init__(child1, child2)

    def visit(self, vars_values):
        return self.child1.visit(vars_values) & self.child2.visit(vars_values)
    
class XOROperationNode(LogicalOperationNode):
    def __init__(self, child1, child2):
        super().__init__(child1, child2)

    def visit(self, vars_values):
        return self.child1.visit(vars_values) ^ self.child2.visit(vars_values)
    
operationPrior = {")":1, "(":1, "&":4, "^":3, "|":2, "~":5}

def int_to_bits(input, length, sequance_reversed=True):
    output = []
    if isinstance(input, np.ndarray):
        for i in range(length):
            output.append((input & 1).astype(np.uint8))
            input = input >> 1
    else:
        for i in range(length):
            output.append(input & 1)
            input = input >> 1
    if sequance_reversed:
        output.reverse()
    return output

def bits_to_int(input, sequence_reversed=False):
    if isinstance(input[0], np.ndarray):
        output = np.zeros(1, dtype=np.uint64)
    elif isinstance(input[0], int):
        output = 0
    else:
        assert False
    if sequence_reversed:
        iterator = input
    else:
        iterator = reversed(input)
    for i in iterator:
        output = (output << 1) | (i & 1)
    return output


def inner_product(a, b, length):
    c = a & b
    res = 0
    for i in range(length):
        res = res ^ c
        c = c >> 1
    res = res & 1
    return res

def concatenate_str_list(str_list):
    if not str_list:
        return ""
    res = str_list[0]
    for i in str_list[1:]:
        res = res + " " + i
    return res

def get_xor_clause_list(variable_num):
    res = []
    for i in range(2**variable_num):
        tmp_list = []
        for _ in range(variable_num):
            tmp_list.append(i & 1)
            i >>= 1
        xor_res = 0
        for j in tmp_list:
            xor_res ^= j
        if xor_res == 1:
            res.append(tmp_list)
    return res