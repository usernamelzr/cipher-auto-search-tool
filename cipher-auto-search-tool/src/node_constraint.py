import copy
from bounding_condition import sequential_encoding
from error_handler import raise_error
from node import OperationNode

class NodeConstraint(object):
    def __init__(self, name, category="diff"):
        # category取值为"diff"或"real"或"linear"
        self.category = category
        self.constraint_name = name

    # 应用于哈希路线搜索模块
    def apply(self, cur_var_num, target_node):
        return cur_var_num, [], []
    
    def apply_d_l(self, cur_var_num, target_node, is_search_diff=True):
        return cur_var_num, [], []
    
class ConstantConstraint(NodeConstraint):
    def __init__(self, target_node_index, bit_index, constant, category="diff"):
        super().__init__("C_CONSTANT", category)
        self.target_node_index = target_node_index
        self.bit_index = copy.deepcopy(bit_index)
        self.constant = constant
    
    # 统一返回
    # cur_var_num: 目前共有变量数（包含了新声明的辅助变量）
    # clauses: 约束的相关子句
    # auxiliary_variables: 用到的辅助变量列表

    def apply(self, cur_var_num, target_node):
        clauses = []
        if self.category not in ["diff", "real"]:
            raise_error("哈希函数路线搜索中不允许设置LINEAR类型的C_CONSTANT约束!")
        if self.category == "diff":
            start_index = 0
        elif self.category == "real":
            start_index = target_node.size
        for i in range(len(self.bit_index)):
            if target_node.cond_vars and (self.category == "real"):
                clauses.append([target_node.cond_vars[self.bit_index[i]]])
            if ((self.constant >> i) & 1) == 1:
                clauses.append([target_node.variables[start_index + self.bit_index[i]]])
            else:
                clauses.append([-1 * target_node.variables[start_index + self.bit_index[i]]])
        return cur_var_num, clauses, []
    
    def apply_d_l(self, cur_var_num, target_node, is_search_diff=True):
        clauses = []
        if self.category not in ["diff", "linear"]:
            raise_error("差分/线性搜索中不允许设置REAL类型的C_CONSTANT约束!")
        if (self.category == "diff" and is_search_diff) or (self.category == "linear" and (not is_search_diff)):
            for i in range(len(self.bit_index)):
                if ((self.constant >> i) & 1) == 1:
                    clauses.append([target_node.variables[self.bit_index[i]]])
                else:
                    clauses.append([-1 * target_node.variables[self.bit_index[i]]])
        return cur_var_num, clauses, []
    
class ConditionConstraint(NodeConstraint):
    def __init__(self, target_node_index, fore_node_index, bit_index, conditions):
        super().__init__("C_CONDITION", "real")
        self.target_node_index = target_node_index
        self.fore_node_index = fore_node_index
        self.bit_index = copy.deepcopy(bit_index)
        self.conditions = conditions
    
    def apply(self, cur_var_num, target_node, fore_node):
        clauses = []
        start_index = target_node.size
        for i in range(len(self.bit_index)):
            if (self.conditions[len(self.bit_index)-i-1]) == '1':
                if target_node.cond_vars:
                    clauses.append([target_node.cond_vars[self.bit_index[i]]])
                clauses.append([target_node.variables[start_index + self.bit_index[i]]])
            elif (self.conditions[len(self.bit_index)-i-1]) == '0':
                if target_node.cond_vars:
                    clauses.append([target_node.cond_vars[self.bit_index[i]]])
                clauses.append([-1 * target_node.variables[start_index + self.bit_index[i]]])
            elif (self.conditions[len(self.bit_index)-i-1]) == 'a':
                if target_node.cond_vars:
                    clauses.append([target_node.cond_vars[self.bit_index[i]]])
                clauses.append([target_node.variables[start_index + self.bit_index[i]], -1 * fore_node.variables[start_index + self.bit_index[i]]])
                clauses.append([-1 * target_node.variables[start_index + self.bit_index[i]], fore_node.variables[start_index + self.bit_index[i]]])
                      
        return cur_var_num, clauses, []
    
class MdiffConstraint(NodeConstraint):
    def __init__(self, target_node_index, bit_index, constant1, constant2):
        super().__init__("C_MDIFF")
        self.target_node_index = target_node_index
        self.bit_index = copy.deepcopy(bit_index)
        self.constant1 = constant1
        self.constant2 = constant2

    def apply(self, cur_var_num, target_node):
        clauses = []
        for i in range(len(self.bit_index)):
            if ((self.constant1 >> i) & 1) == 1:
                clauses.append([target_node.variables[self.bit_index[i]]])
                if ((self.constant2 >> i) & 1) == 1:
                    clauses.append([target_node.variables[target_node.size + self.bit_index[i]]])
                else:
                    clauses.append([-1 * target_node.variables[target_node.size + self.bit_index[i]]])
            else:
                clauses.append([-1 * target_node.variables[self.bit_index[i]]])
        return cur_var_num, clauses, []
    
class UnequalConstantConstraint(NodeConstraint):
    def __init__(self, target_node_index, bit_index, constant, category="diff"):
        super().__init__("C_UNEQUALCONSTANT", category)
        self.target_node_index = target_node_index
        self.bit_index = copy.deepcopy(bit_index)
        self.constant = constant
    
    def apply(self, cur_var_num, target_node):
        clause = []
        if self.category == "diff":
            start_index = 0
        elif self.category == "real":
            start_index = target_node.size
        for i in range(len(self.bit_index)):
            if ((self.constant >> i) & 1) == 1:
                clause.append(-1 * target_node.variables[start_index + self.bit_index[i]])
            else:
                clause.append(target_node.variables[start_index + self.bit_index[i]])
        return cur_var_num, [clause], []
    
class EqualConstraint(NodeConstraint):
    def __init__(self, target_node_index_1, target_node_index_2, bit_index, category="diff"):
        super().__init__("C_EQUAL", category)
        self.target_node_index_1 = target_node_index_1
        self.target_node_index_2 = target_node_index_2
        self.bit_index = copy.deepcopy(bit_index)

    def apply(self, cur_var_num, target_node_1, target_node_2):
        assert target_node_1.size == target_node_2.size
        clauses = []
        if self.category == "diff":
            start_index = 0
        elif self.category == "real":
            start_index = target_node_1.size
        for i in self.bit_index:
            if target_node_2.cond_vars and (self.category == "real"):
                clauses.append([target_node_2.cond_vars[i]])
            clauses.append([target_node_1.variables[start_index + i], -1 * target_node_2.variables[start_index + i]])
            clauses.append([-1 * target_node_1.variables[start_index + i], target_node_2.variables[start_index + i]])
        return cur_var_num, clauses, []
    
class UnequalConstraint(NodeConstraint):
    def __init__(self, target_node_index_1, target_node_index_2, bit_index, category="diff"):
        super().__init__("C_UNEQUAL", category)
        self.target_node_index_1 = target_node_index_1
        self.target_node_index_2 = target_node_index_2
        self.bit_index = copy.deepcopy(bit_index)
    
    def apply(self, cur_var_num, target_node_1, target_node_2):
        assert target_node_1.size == target_node_2.size
        clauses = []
        auxiliary_variables = [i for i in range(cur_var_num, cur_var_num + len(self.bit_index))]
        if self.category == "diff":
            start_index = 0
        elif self.category == "real":
            start_index = target_node_1.size
        x0 = [target_node_1.variables[start_index + i] for i in self.bit_index]
        x1 = [target_node_2.variables[start_index + i] for i in self.bit_index]
        for i in range(len(x0)):
            clauses.append([x0[i], x1[i], -1 * auxiliary_variables[i]])
            clauses.append([x0[i], -1 * x1[i], auxiliary_variables[i]])
            clauses.append([-1 * x0[i], x1[i], auxiliary_variables[i]])
            clauses.append([-1 * x0[i], -1 * x1[i], -1 * auxiliary_variables[i]])
        clauses.append(auxiliary_variables.copy())
        return cur_var_num + len(auxiliary_variables), clauses, auxiliary_variables
    
class ConditionSumConstraint(NodeConstraint):
    def __init__(self, target_node_indexes: list, max_cond_sum: int):
        super().__init__("C_CONDITIONSUM", "cond")
        self.target_node_indexes = copy.deepcopy(target_node_indexes)
        self.max_cond_sum = max_cond_sum

    def apply(self, cur_var_num, target_nodes):
        cond_variables = []
        for node in target_nodes:
            cond_variables += node.cond_vars[:]
        cur_var_num, clauses, s = sequential_encoding(cur_var_num, cond_variables, self.max_cond_sum)
        return cur_var_num, clauses, s

class DiffSumConstraint(NodeConstraint):
    def __init__(self, target_node_indexes: list, max_diff_sum: int):
        super().__init__("C_DIFFSUM", "diff")
        self.target_node_indexes = copy.deepcopy(target_node_indexes)
        self.max_diff_sum = max_diff_sum

    def apply(self, cur_var_num: int, target_nodes: list):
        diff_variables = []
        for node in target_nodes:
            assert len(node.variables) == 2 * node.size
            diff_variables += node.variables[:node.size]
        cur_var_num, clauses, s = sequential_encoding(cur_var_num, diff_variables, self.max_diff_sum)
        return cur_var_num, clauses, s