import numpy as np
import math
import os
import copy
import itertools
import subprocess
import SAT_util
from enum import Enum
from util import *
from error_handler import raise_error

def idc_gen_header_dec(varlist):
    temp1 = ""
    temp = ""
    for i in range(0, len(varlist)):
        temp += "{}, ".format(varlist[i])
    temp = temp[0:-2]
    temp += " : BITVECTOR(1);\n"
    temp1 += temp
    return temp1
# 避免单语句过长，这个还真很多时候不用（思索）

def idc_gen_header_dec_2d(varlist):
    temp1 = ""
    temp = ""
    for i in range(0,len(varlist)):
        for j in range(0, len(varlist[i])):
            temp += "{}, ".format(varlist[i][j])
        temp = temp[0:-2]
        temp += " : BITVECTOR(1);\n"
    temp1 += temp
    return temp1

def idc_gen_end():
    return "QUERY(FALSE);\nCOUNTEREXAMPLE;"

def idc_passRound(parentroundindex,parentindex,childindex,size):
    sen_list=[]
    for j in [0,1]:
        for i in range(size):
            sen_list.append("ASSERT(i_{}_{}_{}_{}=i_{}_{}_{}_{});\n".format(j,i,parentindex,parentroundindex,j,i,childindex,parentroundindex+1))
    return sen_list 

def idc_dec_diff(index,round_index,size,inputdiff):
    sen_list=[]
    for i in range(size):
        sen_list.append("ASSERT(BVXOR(i_0_{}_{}_{}, i_1_{}_{}_{}) = 0bin{});\n".format(i,index,round_index,i,index,round_index,inputdiff[i]))
    return sen_list

def hash_gen_mdiff_conds(variables, cond_vars):
    clauses = []
    for i in range(len(cond_vars)):
        clauses.append([-1 * variables[i], cond_vars[i]])
    return clauses

def get_node_parent_index_list(node):
    parent_index_list = []
    if isinstance(node, SplitNode) or isinstance(node, RotationNode) or isinstance(node, ShiftNode) or isinstance(node, BranchNode) or isinstance(node, EndNode) or isinstance(node, EqualNode) or isinstance(node, SBoxNode) or isinstance(node, PNode):
        # 单父节点
        parent_index_list.append(node.parent_index)
    elif isinstance(node, AddNode):
        # 双父节点
        parent_index_list.append(node.parent_index1)
        parent_index_list.append(node.parent_index2)
    elif isinstance(node, MergeNode) or isinstance(node, FNode) or isinstance(node, ParallelSBoxNode) or isinstance(node, XORNode):
        # 父节点列表
        parent_index_list = node.parent_index_list[:]
    elif isinstance(node, VarRotationNode):
        # 特殊节点VarRotation
        parent_index_list.append(node.parent_index)
        parent_index_list.append(node.case_index)
    return parent_index_list

class OperationNode(object):
    def __init__(self, index, size, node_name):
        self.index = index
        self.size = size
        self.node_name = node_name
        self.variables = []
        self.cond_vars = []

    def idc_vardec_sentence(self,round_index):
        varl=[]
        for i in [0,1]:
            for j in range(0, self.size):
                varl.append("i_{}_{}_{}_{}".format(i, j, self.index, round_index))
        return varl
    # 应统一化，这个声明是任意的,是差分数-位数-节点序号-轮序号

class RootNode(OperationNode):
    def __init__(self, index, size):
        super().__init__(index, size, "ROOT")
    
    # 返回：更新后变量数，新增约束列表，新增计数变量
    def execute(self, cur_var_number):
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        return cur_var_number + self.size, [], []
    
    def idc_execute(self,round_index):
        # root 只用于生成新声明，不必实现
        return []
    
    # 返回：更新后变量数，新增约束列表，新增辅助变量
    def hash_execute(self, cur_var_number, with_cond=False):
        clauses = []
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size * 2)]
        cur_var_number += self.size * 2
        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            clauses += hash_gen_mdiff_conds(self.variables, self.cond_vars)
        return cur_var_number, clauses, []
    
    # 该函数对输入的state进行对应操作的处理
    # RootNode负责随机生成n个状态，返回(self.size, n)大小的比特数组
    def pass_state(self, n):
        new_state = np.frombuffer(os.urandom(self.size * n), dtype=np.uint8).reshape(self.size, n) & 1
        return new_state

class SplitNode(OperationNode):
    def __init__(self, index, size, bit_index, parent_index):
        super().__init__(index, size, "SPLIT")
        self.bit_index = copy.deepcopy(bit_index)
        self.parent_index = parent_index

    def execute(self, cur_var_number, parent):
        self.variables = [parent.variables[i] for i in self.bit_index]
        return cur_var_number, [], []
    
    def idc_execute(self,round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(len(self.bit_index)):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i,self.index,round_index,j,self.bit_index[i],self.parent_index,round_index))
        return sen_list
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        self.variables = [parent.variables[i] for i in self.bit_index] + [parent.variables[i+parent.size] for i in self.bit_index]
        if with_cond:
            self.cond_vars = [parent.cond_vars[i] for i in self.bit_index]
        return cur_var_number, [], []
    
    # SplitNode负责由input比特串得到对应的SPLIT子串
    def pass_state(self, input):
        return [input[i] for i in self.bit_index]

class MergeNode(OperationNode):
    def __init__(self, index, size, parent_index_list):
        super().__init__(index, size, "MERGE")
        self.parent_index_list = copy.deepcopy(parent_index_list)
    
    def execute(self, cur_var_number, parent_list):
        test_bit_counter = 0
        for parent in reversed(parent_list):
            self.variables += parent.variables
            test_bit_counter += parent.size
        if test_bit_counter != self.size:
            raise_error("编号为{}的MERGE节点定义中状态大小与子节点大小之和不一致, 无法进行合并!".format(self.index))
        return cur_var_number, [], []
    
    def hash_execute(self, cur_var_number, parent_list, with_cond=False):
        test_bit_counter = 0
        for parent in reversed(parent_list):
            self.variables += parent.variables[:parent.size]
            test_bit_counter += parent.size
        if test_bit_counter != self.size:
            raise_error("编号为{}的MERGE节点定义中状态大小与子节点大小之和不一致, 无法进行合并!".format(self.index))
        for parent in reversed(parent_list):
            self.variables += parent.variables[parent.size:]
        if with_cond:
            for parent in reversed(parent_list):
                self.cond_vars += parent.cond_vars[:]
        assert len(self.variables) == 2 * self.size
        return cur_var_number, [], []
    
    def idc_execute(self,round_index,parent_list):
        # 不得不传入这个list
        sen_list=[]
        for j in [0,1]:
            counter=0
            for i in reversed(parent_list):
                for t in range(i.size):
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,counter,self.index,round_index,j,t,i.index,round_index))
                    counter+=1
        return sen_list
    
    # MergeNode负责由input_list生成MERGE后的比特串
    def pass_state(self, input_list):
        res = []
        for input in reversed(input_list):
            res += [input[i] for i in range(len(input))]
        if len(res) != self.size:
            raise_error("编号为{}的MERGE节点定义中状态大小与子节点大小之和不一致, 无法进行合并!".format(self.index))
        return res
    
class XORNode(OperationNode):
    def __init__(self, index, size, parent_index_list):
        super().__init__(index, size, "XOR")
        self.parent_index_list = copy.deepcopy(parent_index_list)
    
    def execute(self, cur_var_number, parent_list, is_search_diff=True):
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("编号为{}的XOR操作中, 父节点({})大小({})与子节点大小({})不一致!".format(self.index, parent.index, parent.size, self.size))
        clauses = []
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        if is_search_diff:
            # 约束为各节点异或值为0
            xor_term_num = len(parent_list) + 1
            auxiliary_list = get_xor_clause_list(xor_term_num)
            for i in range(self.size):
                X = [self.variables[i]] + [parent.variables[i] for parent in parent_list]
                for auxiliary_list_entry in auxiliary_list:
                    clauses.append([X[j] if auxiliary_list_entry[j] == 0 else -1 * X[j] for j in range(xor_term_num)])
        else:
            # 约束为父节点分别与子节点相等
            for i in range(self.size):
                for parent in parent_list:
                    clauses.append([parent.variables[i], -1 * self.variables[i]])
                    clauses.append([-1 * parent.variables[i], self.variables[i]])
        return cur_var_number + self.size, clauses, []
    
    def hash_execute(self, cur_var_number, parent_list, with_cond=False):
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("编号为{}的XOR操作中, 父节点({})大小({})与子节点大小({})不一致!".format(self.index, parent.index, parent.size, self.size))
        clauses = []
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size*2)]
        cur_var_number += 2 * self.size
        xor_term_num = len(parent_list) + 1
        auxiliary_list = get_xor_clause_list(xor_term_num)
        for i in range(2 * self.size):
            X = [self.variables[i]] + [parent.variables[i] for parent in parent_list]
            for auxiliary_list_entry in auxiliary_list:
                clauses.append([X[j] if auxiliary_list_entry[j] == 0 else -1 * X[j] for j in range(xor_term_num)])
        # 这个地方还不成熟!!
        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            clauses += hash_gen_mdiff_conds(self.variables, self.cond_vars)
        return cur_var_number, clauses, []
    
    def idc_execute(self,round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(self.size):
                xor_sentence = "i_{}_{}_{}_{}".format(j, i, self.parent_index_list[0], round_index)
                for parent_index in self.parent_index_list[1:]:
                    xor_sentence = "BVXOR(i_{}_{}_{}_{}, {})".format(j, i, parent_index, round_index, xor_sentence)
                sen_list.append("ASSERT({} = i_{}_{}_{}_{});\n".format(xor_sentence, j, i, self.index, round_index))
        return sen_list
    
    # XORNode负责返回所有父节点的异或结果
    def pass_state(self, input_list):
        for input in input_list:
            if len(input) != self.size:
                raise_error("编号为{}的XOR操作中, 父节点大小({})与子节点大小({})不一致!".format(self.index, len(input), self.size))
        output = [0] * self.size
        for input in input_list:
            for bit_index in range(self.size):
                output[bit_index] = output[bit_index] ^ input[bit_index]
        return output

class RotationNode(OperationNode):
    def __init__(self, index, size, parent_index, left_shift_number, is_variable=False):
        super().__init__(index, size, "ROTATION")
        self.is_variable = is_variable
        self.parent_index = parent_index
        # 如果is_variable == True, left_shift_number为一个整数
        # 如果is_variable == False, left_shift_number为一个数组, 保存每一轮的移位数
        self.left_shift_number = copy.deepcopy(left_shift_number)
    
    def execute(self, cur_var_number, parent, round_index=0):
        if parent.size != self.size:
            raise_error("编号为{}的ROTATION节点定义中子节点与父节点状态大小不一致!".format(self.index))
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        self.variables = [parent.variables[(i + self.size - lsn) % self.size] for i in range(self.size)]
        return cur_var_number, [], []
    
    def hash_execute(self, cur_var_number, parent, round_index=0, with_cond=False):
        if parent.size != self.size:
            raise_error("编号为{}的ROTATION节点定义中子节点与父节点状态大小不一致!".format(self.index))
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        self.variables = [parent.variables[(i + self.size - lsn) % self.size] for i in range(self.size)] \
                       + [parent.variables[(i + self.size - lsn) % self.size + self.size] for i in range(self.size)]
        if with_cond:
            self.cond_vars = [parent.cond_vars[(i + self.size - lsn) % self.size] for i in range(self.size)]
        return cur_var_number, [], []
    
    def idc_execute(self,round_index):
        sen_list=[]
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        for j in [0,1]:
            for i in range(self.size):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,(i+lsn+self.size)%self.size,self.index,round_index,j,i,self.parent_index,round_index))
        return sen_list
    
    # RotationNode负责返回input进行ROTATION后的结果
    def pass_state(self, input, round_index=0):
        if len(input) != self.size:
            raise_error("编号为{}的ROTATION节点定义中子节点与父节点状态大小不一致!".format(self.index))
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        return [input[(i + self.size - lsn) % self.size] for i in range(self.size)]
    
# 未验证正确性
class ShiftNode(OperationNode):
    def __init__(self, index, size, parent_index, left_shift_number, is_variable=False):
        super().__init__(index, size, "SHIFT")
        self.parent_index = parent_index
        self.is_variable = is_variable
        self.left_shift_number = copy.deepcopy(left_shift_number)

    def execute(self, cur_var_number, parent, is_search_diff=True, round_index=0):
        if parent.size != self.size:
            raise_error("编号为{}的SHIFT节点定义中子节点与父节点状态大小不一致!".format(self.index))
        clauses = []
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        if abs(lsn) > self.size:
            raise_error("编号为{}的SHIFT节点定义中移位数绝对值大于状态比特数".format(self.index))
        if lsn > 0:
            self.variables = [i for i in range(cur_var_number, cur_var_number + lsn)] + parent.variables[:(self.size - lsn)]
            cur_var_number += lsn
            if is_search_diff:
                for i in range(lsn):
                    clauses.append([-1 * self.variables[i]])
        else:
            self.variables = parent.variables[(-1 * lsn):] + [i for i in range(cur_var_number, cur_var_number - lsn)]
            cur_var_number -= lsn
            if is_search_diff:
                for i in range(self.size + lsn, self.size):
                    clauses.append([-1 * self.variables[i]])
        return cur_var_number, clauses, []
    
    def hash_execute(self, cur_var_number, parent, round_index=0, with_cond=False):
        if parent.size != self.size:
            raise_error("编号为{}的SHIFT节点定义中子节点与父节点状态大小不一致!".format(self.index))
        clauses = []
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        if abs(lsn) > self.size:
            raise_error("编号为{}的SHIFT节点定义中移位数绝对值大于状态比特数".format(self.index))
        if lsn > 0:
            self.variables = [i for i in range(cur_var_number, cur_var_number + lsn)] + parent.variables[:(self.size - lsn)]
            cur_var_number += lsn
            self.variables += [i for i in range(cur_var_number, cur_var_number + lsn)] + parent.variables[self.size : self.size + (self.size - lsn)]
            cur_var_number += lsn
            for i in range(lsn):
                clauses.append([-1 * self.variables[i]])
                clauses.append([-1 * self.variables[i + self.size]])
            if with_cond:
                # 目前实现最低lsn位均有条件
                self.conv_vars = [i for i in range(cur_var_number, cur_var_number + lsn)] + parent.cond_vars[:(self.size - lsn)]
                cur_var_number += lsn
                for i in range(lsn):
                    clauses.append([self.cond_vars[i]])
        else:
            self.variables = parent.variables[(-1 * lsn) : self.size] + [i for i in range(cur_var_number, cur_var_number - lsn)]
            cur_var_number -= lsn
            self.variables += parent.variables[self.size - lsn:] + [i for i in range(cur_var_number, cur_var_number - lsn)]
            cur_var_number -= lsn
            for i in range(self.size + lsn, self.size):
                clauses.append([-1 * self.variables[i]])
                clauses.append([-1 * self.variables[i + self.size]])
            if with_cond:
                # 目前实现高-lsn位均有条件
                self.cond_vars = parent.cond_vars[(-1 * lsn):] + [i for i in range(cur_var_number, cur_var_number - lsn)]
                cur_var_number -= lsn
                for i in range(self.size + lsn, self.size):
                    clauses.append([self.cond_vars[i]])
        return cur_var_number, clauses, []
    
    def idc_execute(self,round_index):
        sen_list=[]
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        if abs(lsn) > self.size:
            raise_error("编号为{}的SHIFT节点定义中移位数绝对值大于状态比特数".format(self.index))
        if lsn<=0:
            # 右移高位置为0，低位变为父节点高位
            for j in [0,1]:
                for i in range(min(-lsn,self.size)):
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = 0bin0);\n".format(j,self.size-i-1,self.index,round_index))
                for i in range(self.size-min(-lsn,self.size)):
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i,self.index,round_index,j,i-lsn,self.parent_index,round_index))
        else:
            # 左移低位置为0，高位变为父节点低位
            for j in [0,1]:
                for i in range(min(lsn,self.size)):
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = 0bin0);\n".format(j,i,self.index,round_index))
                for i in range(self.size-min(lsn,self.size)):
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i+lsn,self.index,round_index,j,i,self.parent_index,round_index))
            
        return sen_list
    
    # ShiftNode负责返回input进行SHIFT操作后的状态
    def pass_state(self, input, round_index):
        if len(input) != self.size:
            raise_error("编号为{}的SHIFT节点定义中子节点与父节点状态大小不一致!".format(self.index))
        if self.is_variable:
            lsn = self.left_shift_number[round_index]
        else:
            lsn = self.left_shift_number
        if abs(lsn) > self.size:
            raise_error("编号为{}的SHIFT节点定义中移位数绝对值大于状态比特数".format(self.index))
        if lsn > 0:
            zero_value = [0] * lsn
            res = zero_value + [input[i] for i in range(self.size - lsn)]
        else:
            zero_value = [0] * (-1 * lsn)
            res = [input[i] for i in range(-1 * lsn, self.size)] + zero_value
        return res

class BranchNode(OperationNode):
    def __init__(self, index, size, parent_index, out_index_list):
        super().__init__(index, size, "BRANCH")
        self.parent_index = parent_index
        self.out_index_list = copy.deepcopy(out_index_list)
    
    def execute(self, cur_var_number, parent, out_list, is_search_diff=True):
        if parent.size != self.size:
            raise_error("BRANCH操作(子节点列表为{})中子节点状态大小与父节点不一致!".format(self.out_index_list))
        if is_search_diff:
            self.variables = parent.variables[:]
            return cur_var_number, [], []
        else:
            self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
            if self.index != max(self.out_index_list):
                return cur_var_number + self.size, [], []
            # 只有编号最大的输出节点负责生成所有约束
            clauses = []
            xor_term_num = len(self.out_index_list) + 1
            auxiliary_list = get_xor_clause_list(xor_term_num)
            for i in range(self.size):
                X = [parent.variables[i]] + [out.variables[i] for out in out_list]
                for auxiliary_list_entry in auxiliary_list:
                    clauses.append([X[j] if auxiliary_list_entry[j] == 0 else -1 * X[j] for j in range(xor_term_num)])
            return cur_var_number + self.size, clauses, []
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        if parent.size != self.size:
            raise_error("BRANCH操作(子节点列表为{})中子节点状态大小与父节点不一致!".format(self.out_index_list))
        self.variables = parent.variables[:]
        if with_cond:
            self.cond_vars = parent.cond_vars[:]
        return cur_var_number, [], []
        
    def idc_execute(self,round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(self.size):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i,self.parent_index, round_index,j,i,self.index, round_index))
        return sen_list
    
    # BranchNode返回和input一样的值
    def pass_state(self, input):
        if len(input) != self.size:
            raise_error("BRANCH操作(子节点列表为{})中子节点状态大小与父节点不一致!".format(self.out_index_list))
        return input

class AddNode(OperationNode):
    def __init__(self, index, size, parent_index1, parent_index2):
        super().__init__(index, size, "ADD")
        self.parent_index1 = parent_index1
        self.parent_index2 = parent_index2
    
    def execute(self, cur_var_number, parent1, parent2, is_search_diff=True):
        if parent1.size != parent2.size or parent1.size != self.size:
            raise_error("编号为{}的ADD节点定义中输入输出状态大小不一致!".format(self.index))
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        cur_var_number += self.size
        clauses = []
        if is_search_diff:
            counter_variables = [i for i in range(cur_var_number, cur_var_number + self.size - 1)]
            cur_var_number += len(counter_variables)
            for i in range(self.size - 1):
                clauses.append([parent1.variables[i], parent2.variables[i], self.variables[i], parent1.variables[i+1], parent2.variables[i+1], -1 * self.variables[i+1]])
                clauses.append([parent1.variables[i], parent2.variables[i], self.variables[i], parent1.variables[i+1], -1 * parent2.variables[i+1], self.variables[i+1]])
                clauses.append([parent1.variables[i], parent2.variables[i], self.variables[i], -1 * parent1.variables[i+1], parent2.variables[i+1], self.variables[i+1]])
                clauses.append([parent1.variables[i], parent2.variables[i], self.variables[i], -1 * parent1.variables[i+1], -1 * parent2.variables[i+1], -1 * self.variables[i+1]])
                clauses.append([-1 * parent1.variables[i], -1 * parent2.variables[i], -1 * self.variables[i], parent1.variables[i+1], parent2.variables[i+1], self.variables[i+1]])
                clauses.append([-1 * parent1.variables[i], -1 * parent2.variables[i], -1 * self.variables[i], parent1.variables[i+1], -1 * parent2.variables[i+1], -1 * self.variables[i+1]])
                clauses.append([-1 * parent1.variables[i], -1 * parent2.variables[i], -1 * self.variables[i], -1 * parent1.variables[i+1], parent2.variables[i+1], -1 * self.variables[i+1]])
                clauses.append([-1 * parent1.variables[i], -1 * parent2.variables[i], -1 * self.variables[i], -1 * parent1.variables[i+1], -1 * parent2.variables[i+1], self.variables[i+1]])
            clauses.append([parent1.variables[0], parent2.variables[0], -1 * self.variables[0]])
            clauses.append([parent1.variables[0], -1 * parent2.variables[0], self.variables[0]])
            clauses.append([-1 * parent1.variables[0], parent2.variables[0], self.variables[0]])
            clauses.append([-1 * parent1.variables[0], -1 * parent2.variables[0], -1 * self.variables[0]])
            for i in range(self.size - 1):
                clauses.append([-1 * parent1.variables[i], self.variables[i], counter_variables[i]])
                clauses.append([parent2.variables[i], -1 * self.variables[i], counter_variables[i]])
                clauses.append([parent1.variables[i], -1 * parent2.variables[i], counter_variables[i]])
                clauses.append([parent1.variables[i], parent2.variables[i], self.variables[i], -1 * counter_variables[i]])
                clauses.append([-1 * parent1.variables[i], -1 * parent2.variables[i], -1 * self.variables[i], -1 * counter_variables[i]])
            return cur_var_number, clauses, counter_variables
        else:
            counter_variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += len(counter_variables)
            clauses.append([-1 * counter_variables[self.size-1]])
            auxiliary_list = get_xor_clause_list(4)
            variable_list = [parent1.variables[self.size-1], parent2.variables[self.size-1], self.variables[self.size-1], counter_variables[self.size-2]]
            for value_list in auxiliary_list:
                clause = []
                for i in range(4):
                    clause.append(variable_list[i] if value_list[i] == 0 else -1 * variable_list[i])
                clauses.append(clause)
            auxiliary_list = get_xor_clause_list(5)
            variable_list = [parent1.variables[1:], parent2.variables[1:], self.variables[1:], counter_variables[1:], counter_variables]
            for j in range(self.size - 2):
                for value_list in auxiliary_list:
                    clause = []
                    for i in range(5):
                        clause.append(variable_list[i][j] if value_list[i] == 0 else -1 * variable_list[i][j])
                    clauses.append(clause)
            for i in range(self.size):
                clauses.append([parent1.variables[i], -1 * self.variables[i], counter_variables[i]])
                clauses.append([-1 * parent1.variables[i], self.variables[i], counter_variables[i]])
                clauses.append([parent2.variables[i], -1 * self.variables[i], counter_variables[i]])
                clauses.append([-1 * parent2.variables[i], self.variables[i], counter_variables[i]])
            return cur_var_number, clauses, counter_variables
        
    def hash_execute(self, cur_var_number, parent1, parent2, with_cond=False):
        if parent1.size != parent2.size or parent1.size != self.size:
            raise_error("编号为{}的ADD节点定义中输入输出状态大小不一致!".format(self.index))
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size*2)]
        cur_var_number += self.size*2
        clauses = []
        carry_variables = [i for i in range(cur_var_number, cur_var_number + (self.size + 1)*2)]
        cur_var_number += len(carry_variables)
              
        SymbolicCNFConstraintForadd = [[9, 9, 9, 0, 1, 1, 9, 1, 9, 9],[9, 9, 9, 1, 0, 1, 9, 1, 9, 9],[9, 9, 9, 1, 1, 0, 9, 1, 9, 9],[9, 9, 9, 1, 1, 1, 9, 0, 9, 9],[1, 1, 1, 9, 9, 9, 0, 9, 9, 9],[9, 9, 9, 0, 0, 0, 9, 1, 9, 9],[0, 0, 0, 9, 9, 9, 1, 9, 9, 9],[9, 9, 9, 0, 0, 1, 9, 0, 9, 9],[9, 9, 9, 0, 1, 0, 9, 0, 9, 9],[9, 9, 9, 1, 0, 0, 9, 0, 9, 9],[9, 0, 0, 9, 9, 9, 9, 9, 1, 9],[9, 1, 1, 9, 9, 9, 9, 9, 0, 9],[0, 9, 9, 9, 9, 9, 1, 9, 1, 9],[1, 9, 9, 9, 9, 9, 0, 9, 0, 9],[1, 0, 1, 9, 9, 9, 1, 9, 9, 9],[1, 1, 0, 9, 9, 9, 1, 9, 9, 9],[0, 0, 1, 9, 9, 9, 0, 9, 9, 9],[0, 1, 0, 9, 9, 9, 0, 9, 9, 9],[0, 1, 9, 9, 9, 0, 9, 0, 9, 1],[0, 9, 1, 9, 1, 9, 9, 1, 9, 0],[1, 9, 0, 9, 1, 9, 9, 1, 9, 0],[1, 9, 9, 9, 0, 0, 1, 9, 9, 1],[0, 9, 9, 9, 0, 0, 0, 9, 9, 1],[9, 1, 1, 9, 1, 1, 9, 9, 9, 0],[9, 0, 9, 9, 0, 9, 1, 0, 9, 1],[9, 9, 1, 9, 9, 1, 0, 1, 9, 0],[0, 9, 0, 1, 9, 1, 9, 9, 9, 0],[1, 9, 9, 0, 9, 9, 0, 0, 9, 1],[1, 0, 9, 9, 9, 0, 9, 0, 9, 1],[9, 0, 1, 1, 9, 9, 9, 1, 9, 0],[9, 1, 0, 1, 9, 9, 9, 1, 9, 0],[9, 9, 0, 0, 0, 9, 0, 9, 9, 1],[9, 0, 9, 0, 9, 0, 0, 9, 9, 1],[9, 9, 9, 0, 9, 9, 1, 1, 1, 1],[9, 1, 9, 0, 1, 9, 9, 9, 0, 1],[9, 9, 1, 0, 9, 1, 9, 9, 0, 1],[1, 9, 1, 1, 9, 1, 9, 9, 9, 0],[1, 1, 9, 1, 1, 9, 9, 9, 9, 0],[9, 0, 0, 9, 1, 1, 9, 9, 9, 0],[0, 0, 9, 1, 1, 9, 9, 9, 9, 0],[9, 1, 9, 9, 0, 9, 0, 0, 9, 1],[9, 9, 0, 9, 9, 1, 1, 1, 9, 0]]            
        
        da = [parent1.variables[i] for i in range(parent1.size)]
        a0 = [parent1.variables[i+parent1.size] for i in range(parent1.size)]
        db = [parent2.variables[i] for i in range(parent2.size)]
        b0 = [parent2.variables[i+parent2.size] for i in range(parent2.size)]
        dc = [carry_variables[i] for i in range(self.size+1)]
        c0 = [carry_variables[i+self.size+1] for i in range(self.size+1)]
        ds = [self.variables[i] for i in range(self.size)]
        s0 = [self.variables[i+self.size] for i in range(self.size)]

        clauses.append([-1 * dc[0]])
        clauses.append([-1 * c0[0]])        
        for i in  range(self.size):
            X = [a0[i],b0[i],c0[i],da[i],db[i],dc[i],s0[i],ds[i],c0[i+1],dc[i+1]]
            for j in range(len(SymbolicCNFConstraintForadd)): #42
                clause = []
                for k in range(len(X)): #10
                    if (SymbolicCNFConstraintForadd[j][k] == 0):
                        clause.append(X[k])
                    if (SymbolicCNFConstraintForadd[j][k] == 1):
                        clause.append(-1 * X[k])
                clauses.append(clause)

        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            clauses += hash_gen_mdiff_conds(self.variables, self.cond_vars)

        return cur_var_number, clauses, carry_variables
        
    def idc_execute(self,round_index):
        sen_list=[]
        # 拼接与生成
        for j in [0,1]:
            var1=""
            var2=""
            var3=""
            for i in range(self.size):
                var1="i_{}_{}_{}_{}@".format(j,i,self.parent_index1, round_index)+var1
                var2="i_{}_{}_{}_{}@".format(j,i,self.parent_index2, round_index)+var2
                var3="i_{}_{}_{}_{}@".format(j,i,self.index, round_index)+var3
            sen_list.append("ASSERT(BVPLUS({},{},{}) = {});\n".format(self.size,var1[:-1],var2[:-1],var3[:-1]))
        return sen_list
    
    # AddNode负责返回input1和input2两输入状态的和，只支持64位以内的加法
    def pass_state(self, input1, input2):
        if len(input1) != len(input2) or len(input1) != self.size:
            raise_error("编号为{}的ADD节点定义中输入输出状态大小不一致!".format(self.index))
        if self.size > 64:
            raise_error("计算ADD节点{}中, 不支持大于64位加法操作!".format(self.index))
        input1_int = bits_to_int(input1)
        input2_int = bits_to_int(input2)
        res = input1_int + input2_int
        return int_to_bits(res, self.size, False)
    
class ConstantNode(OperationNode):
    def __init__(self, index, size, constant, is_variable=False):
        super().__init__(index, size, "CONSTANT")
        self.constant = copy.deepcopy(constant)
        self.is_variable = is_variable

    def get_constant(self, round_index):
        if self.is_variable:
            return self.constant[round_index]
        return self.constant

    def execute(self, cur_var_number, round_index, is_search_diff=True):
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        clauses = []
        if is_search_diff:
            for i in self.variables:
                clauses.append([-1 * i])
        return cur_var_number + self.size, clauses, []
    
    def hash_execute(self, cur_var_number, round_index, with_cond=False):
        self.variables = [i for i in range(cur_var_number, cur_var_number + 2 * self.size)]
        cur_var_number += 2 * self.size
        clauses = []
        if self.is_variable:
            if round_index not in self.constant:
                raise_error("轮常数节点{}在第{}轮中无定义!".format(self.index, round_index))
            constant = self.constant[round_index]
        else:
            constant = self.constant
        # 常数差分为0
        for i in self.variables[:self.size]:
            clauses.append([-1 * i])
        # 真实值设置为constant
        for i in range(self.size):
            if (constant >> i) & 1 == 1:
                clauses.append([self.variables[self.size + i]])
            else:
                clauses.append([-1 * self.variables[self.size + i]])
        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            for i in range(self.size):
                clauses.append([self.cond_vars[i]])
        return cur_var_number, clauses, []
    
    def idc_execute(self, round_index):
        sen_list = []
        if self.is_variable:
            if round_index not in self.constant:
                raise_error("轮常数节点{}在第{}轮中无定义!".format(self.index, round_index))
            constant = self.constant[round_index]
        else:
            constant = self.constant
        for j in [0, 1]:
            for i in range(self.size):
                if (constant >> i) & 1 == 1:
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = 0bin1);\n".format(j, i, self.index, round_index))
                else:
                    sen_list.append("ASSERT(i_{}_{}_{}_{} = 0bin0);\n".format(j, i, self.index, round_index))
        return sen_list
    
    def pass_state(self, round_index):
        res = []
        if self.is_variable:
            if round_index not in self.constant:
                raise_error("轮常数节点{}在第{}轮中无定义!".format(self.index, round_index))
            constant = self.constant[round_index]
        else:
            constant = self.constant
        for i in range(self.size):
            if (constant >> i) & 1 == 1:
                res.append(1)
            else:
                res.append(0)
        return res

class EndNode(OperationNode):
    def __init__(self, index, size, parent_index):
        super().__init__(index, size, "END")
        self.parent_index = parent_index
    
    def execute(self, cur_var_number, parent):
        if self.size != parent.size:
            raise_error("编号为{}的END节点父节点与子节点大小不一致!".format(self.index))
        self.variables = parent.variables[:]
        return cur_var_number, [], []
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        if self.size != parent.size:
            raise_error("编号为{}的END节点父节点与子节点大小不一致!".format(self.index))
        self.variables = parent.variables[:]
        if with_cond:
            self.cond_vars = parent.cond_vars[:]
        return cur_var_number, [], []
    
    def idc_execute(self,round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(self.size):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i,self.parent_index, round_index,j,i,self.index, round_index))
        return sen_list
    
    # EndNode返回与input一样的值
    def pass_state(self, input):
        return input

class EqualNode(OperationNode):
    def __init__(self, index, size, parent_index):
        super().__init__(index, size, "EQUAL")
        self.parent_index = parent_index
    
    def execute(self, cur_var_number, parent):
        if self.size != parent.size:
            raise_error("编号为{}的EQUAL节点父节点与子节点大小不一致!".format(self.index))
        self.variables = parent.variables[:]
        return cur_var_number, [], []
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        if self.size != parent.size:
            raise_error("编号为{}的EQUAL节点父节点与子节点大小不一致!".format(self.index))
        self.variables = parent.variables[:]
        if with_cond:
            self.cond_vars = parent.cond_vars[:]
        return cur_var_number, [], []
    
    def idc_execute(self, round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(self.size):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,i,self.parent_index, round_index,j,i,self.index, round_index))
        return sen_list
    
    def pass_state(self, input):
        return input
    
class ParallelSBoxNode(OperationNode):
    def __init__(self, index, size, input_length, output_length, parent_index_list, output_index_list):
        super().__init__(index, size, "PSBOX")
        self.parent_index_list = copy.deepcopy(parent_index_list)
        self.output_index_list = copy.deepcopy(output_index_list)
        self.input_length = input_length
        self.output_length = output_length
        self.counter_var_length_diff = 0
        self.counter_var_length_linear = 0
        self.sbox_clauses_real = None
        self.sbox_clauses_diff = None
        self.sbox_clauses_linear = None
        self.sbox_clauses_diff_real = None
        self.lookup_table = None

    def inherit_from_SBoxNode(self, node):
        assert isinstance(node, SBoxNode)
        self.counter_var_length_diff = node.counter_var_length_diff
        self.counter_var_length_linear = node.counter_var_length_linear
        self.sbox_clauses_real = node.sbox_clauses_real
        self.sbox_clauses_diff = node.sbox_clauses_diff
        self.sbox_clauses_linear = node.sbox_clauses_linear
        self.sbox_clauses_diff_real = node.sbox_clauses_diff_real
        self.lookup_table = node.lookup_table
    
    def execute(self, cur_var_number, parent_list, output_list, is_search_diff=True):
        # 保证所有节点大小一样，因为需要逐比特运算
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("PSBOX操作中父节点{}与子节点{}的状态大小不一致!".format(parent.size, self.size))
        # 首先需要声明变量
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        cur_var_number += self.size
        if self.index != max(self.output_index_list):
            return cur_var_number, [], []
        # 目前是ParallelSBox兄弟节点中下标最大的，可以开始生成约束
        clauses = []
        sbox_clauses = self.sbox_clauses_diff if is_search_diff else self.sbox_clauses_linear
        counter_var_length = self.counter_var_length_diff if is_search_diff else self.counter_var_length_linear
        counter_variables = []
        key_length = self.input_length + self.output_length + counter_var_length
        # 按比特生成S盒的约束
        for bit_index in range(self.size):
            sub_counter_variables = [i for i in range(cur_var_number, cur_var_number + counter_var_length)]
            cur_var_number += counter_var_length
            counter_variables += sub_counter_variables
            key_variables = [parent.variables[bit_index] for parent in parent_list] + [output.variables[bit_index] for output in output_list] + [i for i in reversed(sub_counter_variables)]
            for sbox_clause in sbox_clauses:
                clause = []
                assert key_length == len(sbox_clause)
                for i in range(key_length):
                    if sbox_clause[i] == 1:
                        clause.append(key_variables[i])
                    elif sbox_clause[i] == -1:
                        clause.append(-1 * key_variables[i])
                clauses.append(clause)
        return cur_var_number, clauses, counter_variables
    
    def pass_state(self, parent_input_list):
        assert len(parent_input_list) == self.input_length
        for parent_input in parent_input_list:
            if len(parent_input) != self.size:
                raise_error("PSBOX操作中父节点与子节点{}的状态大小不一致!".format(self.index))
        # 让最小的输出节点进行计算
        if self.index != min(self.output_index_list):
            return []
        output = [[] for _ in range(self.output_length)]
        for i in range(self.size):
            sbox_input = bits_to_int([parent_input[i] for parent_input in parent_input_list], True)
            sbox_output = self.lookup_table[sbox_input]
            if isinstance(sbox_input, int):
                sbox_output = int(sbox_output)
            sbox_output_bits = int_to_bits(sbox_output, self.output_length, True)
            for j in range(self.output_length):
                output[j].append(sbox_output_bits[j])
        return output
    
    def hash_execute(self, cur_var_number, parent_list, output_list, with_cond=False):
        if with_cond:
            # S 盒目前不支持条件数控制
            raise_error("哈希函数中检测到S盒操作, 目前不支持条件控制!")
        # 保证所有节点大小一样，因为需要逐比特运算
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("PSBOX操作中父节点{}与子节点{}的状态大小不一致!".format(parent.size, self.size))
        # 首先需要声明变量
        self.variables = [i for i in range(cur_var_number, cur_var_number + 2 * self.size)]
        cur_var_number += 2 * self.size
        if self.index != max(self.output_index_list):
            return cur_var_number, [], []
        clauses = []
        key_length = 2 * (self.input_length + self.output_length)
        for bit_index in range(self.size):
            key_variables = [parent.variables[bit_index] for parent in parent_list] + [parent.variables[self.size + bit_index] for parent in parent_list] + [output.variables[bit_index] for output in output_list] + [output.variables[self.size + bit_index] for output in output_list]
            for sbox_clause in self.sbox_clauses_diff_real:
                clause = []
                assert len(sbox_clause) == key_length
                for i in range(key_length):
                    if sbox_clause[i] == 1:
                        clause.append(key_variables[i])
                    elif sbox_clause[i] == -1:
                        clause.append(-1 * key_variables[i])
                clauses.append(clause)
        return cur_var_number, clauses, []
    
    def idc_execute(self, round_index, parent_list):
        sen_list = []
        # 保证所有节点大小一样，因为需要逐比特运算
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("PSBOX操作中父节点{}与子节点{}的状态大小不一致!".format(parent.size, self.size))
        if self.index != max(self.output_index_list):
            # 只有编号最大的输出节点负责生成约束
            return []
        for bit_index in range(self.size):
            for j in [0, 1]:
                for row in self.sbox_clauses_real:
                    temp = ""
                    for u in range(self.input_length):
                        if row[u] == 1:
                            temp += "i_{}_{}_{}_{}|".format(j, bit_index, self.parent_index_list[u], round_index)
                        elif row[u] == -1:
                            temp += "~i_{}_{}_{}_{}|".format(j, bit_index, self.parent_index_list[u], round_index)
                    for v in range(self.output_length):
                        if row[self.input_length + v] == 1:
                            temp += "i_{}_{}_{}_{}|".format(j, bit_index, self.output_index_list[v], round_index)
                        elif row[self.input_length + v] == -1:
                            temp += "~i_{}_{}_{}_{}|".format(j, bit_index, self.output_index_list[v], round_index)
                    temp = temp[:-1]
                    sen_list.append("ASSERT(({}) = 0bin1);\n".format(temp))
        return sen_list

    
class SBoxNode(OperationNode):
    def __init__(self, index, input_length, output_length, lookup_table, parent_index):
        super().__init__(index, output_length, "SBOX")
        self.parent_index = parent_index
        self.input_length = input_length
        self.output_length = output_length
        # real为真实值模型，用不到counter_var
        # diff_real为模差分模型, 用不到counter_var
        self.counter_var_length_diff = 0
        self.counter_var_length_linear = 0
        self.sbox_clauses_real = None
        self.sbox_clauses_diff = None
        self.sbox_clauses_linear = None
        self.sbox_clauses_diff_real = None
        self.lookup_table = np.array(lookup_table, dtype=np.uint32)

    def execute(self, cur_var_number, parent, is_search_diff=True):
        if parent.size != self.input_length:
            raise_error("编号为{}的SBOX操作中父节点{}大小与{}定义的输入大小不一致!".format(self.index, parent.index, self.input_length))
        sbox_clauses = self.sbox_clauses_diff if is_search_diff else self.sbox_clauses_linear
        counter_var_length = self.counter_var_length_diff if is_search_diff else self.counter_var_length_linear
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.output_length)]
        cur_var_number += self.output_length
        counter_variables = [i for i in range(cur_var_number, cur_var_number + counter_var_length)]
        cur_var_number += counter_var_length
        key_variables = [i for i in reversed(parent.variables)] + [i for i in reversed(self.variables)] + [i for i in reversed(counter_variables)]
        clauses = []
        for sbox_clause in sbox_clauses:
            clause = []
            for i in range(len(key_variables)):
                if sbox_clause[i] == 1:
                    clause.append(key_variables[i])
                elif sbox_clause[i] == -1:
                    clause.append(-1 * key_variables[i])
            clauses.append(clause)
        return cur_var_number, clauses, counter_variables
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        if with_cond:
            # S 盒目前不支持条件数控制
            raise_error("哈希函数中检测到S盒操作, 目前不支持条件控制!")
        if parent.size != self.input_length:
            raise_error("编号为{}的SBOX操作中父节点{}大小与{}定义的输入大小不一致!".format(self.index, parent.index, self.input_length))
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size * 2)]
        clauses = []
        key_variables = [i for i in reversed(parent.variables[:parent.size])] + [i for i in reversed(parent.variables[parent.size:])] + [i for i in reversed(self.variables[:self.size])] + [i for i in reversed(self.variables[self.size:])]
        for sbox_clause in self.sbox_clauses_diff_real:
            clause = []
            for i in range(len(key_variables)):
                if sbox_clause[i] == 1:
                    clause.append(key_variables[i])
                elif sbox_clause[i] == -1:
                    clause.append(-1 * key_variables[i])
            clauses.append(clause)
        return cur_var_number + 2 * self.size, clauses, []
    
    def idc_execute(self,round_index):
            s_box_statement = []
            for j in [0,1]:
                for row in self.sbox_clauses_real:
                    temp = ""
                    for u in range(0, self.input_length):
                        if row[u] == 1:
                            temp += "i_{}_{}_{}_{}|".format(j,self.input_length-1-u,self.parent_index,round_index)
                        elif row[u] == -1:
                            temp += "(~i_{}_{}_{}_{})|".format(j,self.input_length-1-u,self.parent_index,round_index)
                    for v in range(0, self.output_length):
                        if row[v + self.input_length] == 1:
                            temp += "i_{}_{}_{}_{}|".format(j,self.output_length-1-v,self.index,round_index)
                        elif row[v + self.input_length] == -1:
                            temp += "(~i_{}_{}_{}_{})|".format(j,self.output_length-1-v,self.index,round_index)
                    temp = temp[0:-1]
                    s_box_statement.append("ASSERT(({}) = 0bin1);\n".format(temp))
            return s_box_statement
    
    # SBoxNode返回input经过S盒后的结果
    def pass_state(self, input):
        if len(input) != self.input_length:
            raise_error("编号为{}的SBOX操作中父节点{}大小与{}定义的输入大小不一致!".format(self.index, self.parent_index, self.input_length))
        input_int = bits_to_int(input)
        res = self.lookup_table[input_int]
        if isinstance(input_int, int):
            res = int(res)
        return int_to_bits(res, self.output_length, False)

    # 构建S盒的分析子句, 同时赋值对应的counter_var_length和sbox_clauses
    # 支持分析类型search_type包括: "diff", 差分模型; "linear", 线性模型; "real", 真实值模型; "diff_real", 模差分模型
    # 对于概率模型diff以及linear, 支持使用whether_consider_pr参数设置是否值考虑活跃S盒，不考虑每个传播模式的具体概率
    def build_sbox_clauses(self, search_type="diff", whether_consider_pr=True):
        # search_type选项支持三种值
        assert search_type in ["diff", "linear", "real", "diff_real"]
        input_space = 2 ** self.input_length
        output_space = 2 ** self.output_length
        input_len = self.input_length
        output_len = self.output_length
        if search_type == "diff_real":
            input_space = input_space**2
            output_space = output_space**2
            input_len *= 2
            output_len *= 2
        sbox_lookup_table = self.lookup_table
        # 生成分析表AT
        AT = np.zeros((input_space, output_space), dtype=np.uint32)
        if search_type == "real":
            for in_val in range(input_space):
                AT[in_val][sbox_lookup_table[in_val]] = input_space
        elif search_type == "diff":
            for in_diff in range(input_space):
                for a in range(input_space):
                    b = a ^ in_diff
                    out_diff = sbox_lookup_table[a] ^ sbox_lookup_table[b]
                    AT[in_diff][out_diff] += 1
        elif search_type == "linear":
            input_val = np.arange(input_space, dtype=np.uint32)
            output_val = sbox_lookup_table[input_val]
            for in_mask in range(input_space):
                for out_mask in range(output_space):
                    AT[in_mask][out_mask] = 2 * abs(np.sum(inner_product(input_val, in_mask, input_len) == inner_product(output_val, out_mask, output_len)) - (input_space / 2))
        else:
            input_val1 = np.arange(2**self.input_length, dtype=np.uint32)
            output_val1 = sbox_lookup_table[input_val1]
            for input_diff in range(2**self.input_length):
                input_val2 = input_val1 ^ input_diff
                output_val2 = sbox_lookup_table[input_val2]
                output_diff = output_val1 ^ output_val2
                input_val = (input_diff << self.input_length) | input_val1
                output_val = (output_diff << self.output_length) | output_val1
                for i in range(len(input_val)):
                    AT[input_val[i]][output_val[i]] = input_space
        p_min = input_space
        for row in AT:
            for i in row:
                if i > 0 and i < p_min:
                    p_min = i
        w_num = math.ceil(-1 * math.log2(p_min / input_space))
        if search_type in ["diff", "linear"] and not whether_consider_pr:
            w_num = 1
        # 生成非法赋值集
        if search_type == "real" or search_type == "diff_real":
            assert w_num == 0
        key_length = input_len + output_len + w_num

        allow_set = set()
        illegal_list = []
        for in_val in range(input_space):
            for out_val in range(output_space):
                if AT[in_val][out_val] > 0:
                    p = math.ceil(-1 * math.log2(AT[in_val][out_val] / input_space))
                    key = (in_val << output_len) | out_val
                    key <<= w_num
                    if search_type in ["diff", "linear"] and not whether_consider_pr and p > 0:
                        p = 1
                    for i in range(p):
                        key |= 1 << i
                    allow_set.add(key)
        for key in range(2**key_length):
            if key not in allow_set:
                illegal_list.append(int_to_bits(key, key_length))
        # 生成espresso输入文件
        with open("espresso_input.in", mode="w", encoding="utf-8") as f:
            f.write(f".i {key_length}\n.o 1\n")
            f.write(".ilb")
            for i in reversed(range(input_len)):
                f.write(f" I{i}")
            for i in reversed(range(output_len)):
                f.write(f" O{i}")
            for i in reversed(range(w_num)):
                f.write(f" W{i}")
            f.write("\n.ob F\n")
            for illegal_assignment in illegal_list:
                for i in illegal_assignment:
                    f.write(str(i))
                f.write(" 1\n")
            f.write(".e")
        # 使用espresso分析，解析输出文件
        sbox_clauses = []
        res = subprocess.call(SAT_util.espresso_cmd + " espresso_input.in > espresso_output.out", env=SAT_util.env_para, shell=True)
        with open("espresso_output.out", mode="r", encoding="utf-8") as f:
            line = f.readline().split()
            while line[0] != ".p":
                line = f.readline().split()
            clause_number = int(line[1])
            for i in range(clause_number):
                line = f.readline().split()
                clause_str = line[0]
                assert len(clause_str) == key_length
                clause_val = []
                for ch in clause_str:
                    if ch == "1":
                        clause_val.append(-1)
                    elif ch == "0":
                        clause_val.append(1)
                    elif ch == "-":
                        clause_val.append(0)
                sbox_clauses.append(clause_val)
        # 删除输入输出文件
        os.system(SAT_util.del_cmd + " espresso_input.in")
        os.system(SAT_util.del_cmd + " espresso_output.out")
        # 构造SBoxNode
        if search_type == "real":
            self.sbox_clauses_real = sbox_clauses
        elif search_type == "diff":
            self.sbox_clauses_diff = sbox_clauses
            self.counter_var_length_diff = w_num
        elif search_type == "linear":
            self.sbox_clauses_linear = sbox_clauses
            self.counter_var_length_linear = w_num
        elif search_type == "diff_real":
            self.sbox_clauses_diff_real = sbox_clauses

class SupportedCondF(Enum):
    # 在这里定义支持分析条件的F函数类型
    UNDEFINED = 1
    IF = 2
    XOR = 3
    ONZ = 4

    
class FNode(OperationNode):
    def __init__(self, index, size, parent_index_list, var_num, expression_str):
        super().__init__(index, size, "F")
        self.parent_index_list = copy.deepcopy(parent_index_list)
        self.var_num = var_num
        self.counter_var_length_diff = 0
        self.counter_var_length_linear = 0
        self.function_clauses_diff = None
        self.function_clauses_linear = None
        self.function_clauses = None
        self.cond_f_kind = SupportedCondF.UNDEFINED
        self.f_cond_permutation = []
        # 构造查找表
        # 去除非法符号
        expression_list = ["("]
        for ch in expression_str:
            if FNode.is_operand(ch, var_num) or FNode.is_operation(ch) or ch == "(" or ch == ")":
                expression_list.append(ch)
        expression_list.append(")")
        root_node = FNode.build_operation_tree(expression_list, var_num)
        self.lookup_table = np.zeros(2**var_num, dtype=np.uint8)
        for input_val in range(2**var_num):
            values = int_to_bits(input_val, var_num, True)
            vars_values = dict()
            for i in range(var_num):
                vars_values[chr(ord("a") + i)] = values[i] 
            self.lookup_table[input_val] = root_node.visit(vars_values) & 1
        # 判断F函数是否已知
        lookup_table_if = np.array([0, 1, 0, 1, 0, 0, 1, 1], dtype=np.uint8)
        lookup_table_xor = np.array([0, 1, 1, 0, 1, 0, 0, 1], dtype=np.uint8)
        lookup_table_onz = np.array([1, 0, 0, 1, 1, 0, 1, 0], dtype=np.uint8)
        if self.var_num == 3:
            for perm in itertools.permutations([0,1,2]):
                base_input_val = []
                for input_val in range(8):
                    values = int_to_bits(input_val, 3, True)
                    base_values = [values[perm[i]] for i in range(3)]
                    base_input_val.append(bits_to_int(base_values, True))
                base_input_val = np.array(base_input_val, dtype=np.uint32)
                if np.sum(self.lookup_table == lookup_table_if[base_input_val]) == 8:
                    # 解析到IF函数
                    self.cond_f_kind = SupportedCondF.IF
                    self.f_cond_permutation = perm
                    break
            if np.sum(self.lookup_table == lookup_table_xor) == 8:
                # 解析到XOR函数
                self.cond_f_kind = SupportedCondF.XOR
            if np.sum(self.lookup_table == lookup_table_onz) == 8:
                # 解析到XOR函数
                self.cond_f_kind = SupportedCondF.ONZ 
        

    @staticmethod
    def is_operand(ch, var_num):
        return ord(ch) >= ord("a") and ord(ch) < ord("a") + var_num

    @staticmethod
    def is_operation(ch):
        return ch == "|" or ch == "&" or ch == "~" or ch == "^"
    
    @staticmethod
    def apply_if_cond(var_b, var_c, var_d, var_f, cond_b, cond_c, cond_d):
        clauses = []
        size = len(cond_b)
        d_b = var_b[:size]
        d_c = var_c[:size]
        d_d = var_d[:size]
        d_f = var_f[:size]
        for i in range(size):
            # condB
            clauses.append([d_f[i], d_b[i], -1 * d_c[i], d_d[i], cond_b[i]])
            clauses.append([d_f[i], d_b[i], d_c[i], -1 * d_d[i], cond_b[i]])
            clauses.append([-1 * d_f[i], d_b[i], d_c[i], -1 * d_d[i], cond_b[i]])
            clauses.append([-1 * d_f[i], d_b[i], -1 * d_c[i], d_d[i], cond_b[i]])
            clauses.append([-1 * d_f[i], d_b[i], -1 * d_c[i], -1 * d_d[i], cond_b[i]])
            # condC
            clauses.append([d_f[i], -1 * d_b[i], d_c[i], d_d[i], cond_c[i]])
            clauses.append([d_f[i], -1 * d_b[i], d_c[i], -1 * d_d[i], cond_c[i]])
            clauses.append([-1 * d_f[i], -1 * d_b[i], d_c[i], d_d[i], cond_c[i]])
            clauses.append([-1 * d_f[i], -1 * d_b[i], d_c[i], -1 * d_d[i], cond_c[i]])
            # condD
            clauses.append([d_f[i], -1 * d_b[i], d_c[i], d_d[i], cond_d[i]])
            clauses.append([d_f[i], -1 * d_b[i], -1 * d_c[i], d_d[i], cond_d[i]])
            clauses.append([-1 * d_f[i], -1 * d_b[i], d_c[i], d_d[i], cond_d[i]])
            clauses.append([-1 * d_f[i], -1 * d_b[i], -1 * d_c[i], d_d[i], cond_d[i]])
        return clauses
    
    @staticmethod
    def apply_xor_cond(var_b, var_c, var_d, var_f, cond_b, cond_c, cond_d):
        clauses = []
        size = len(cond_b)
        d_b = var_b[:size]
        d_c = var_c[:size]
        d_d = var_d[:size]
        d_f = var_f[:size]
        for i in range(size):
            # condC
            clauses.append([-1 * d_b[i], d_c[i], d_d[i], -1 * d_f[i], cond_c[i]])
            # condB
            clauses.append([d_b[i], -1 * d_c[i], d_d[i], -1 * d_f[i], cond_b[i]])
            clauses.append([d_b[i], d_c[i], -1 * d_d[i], -1 * d_f[i], cond_b[i]])
        return clauses

    @staticmethod
    def apply_onz_cond(var_b, var_c, var_d, var_f, cond_b, cond_c, cond_d):
        clauses = []
        size = len(cond_b)
        d_b = var_b[:size]
        d_c = var_c[:size]
        d_d = var_d[:size]
        d_f = var_f[:size]
        for i in range(size):
            clauses.append([-1 * d_b[i], d_c[i], d_d[i], d_f[i], cond_c[i]])
            clauses.append([-1 * d_b[i], d_c[i], d_d[i], -1 * d_f[i], cond_c[i]])
            clauses.append([-1 * d_b[i], d_c[i], d_d[i], -1 * d_f[i], cond_d[i]])
            clauses.append([d_b[i], -1 * d_c[i], d_d[i], d_f[i], cond_b[i]])
            clauses.append([d_b[i], -1 * d_c[i], d_d[i], -1 * d_f[i], cond_b[i]])
            clauses.append([d_b[i], -1 * d_c[i], d_d[i], -1 * d_f[i], cond_d[i]])
            clauses.append([-1 * d_b[i], -1 * d_c[i], d_d[i], -1 * d_f[i], cond_d[i]])
            clauses.append([d_b[i], d_c[i], -1 * d_d[i], d_f[i], cond_c[i]])
            clauses.append([-1 * d_b[i], d_c[i], -1 * d_d[i], d_f[i], cond_c[i]])
            clauses.append([-1 * d_b[i], d_c[i], -1 * d_d[i], -1 * d_f[i], cond_c[i]])
            clauses.append([d_b[i], -1 * d_c[i], -1 * d_d[i], d_f[i], cond_b[i]])
            clauses.append([d_b[i], -1 * d_c[i], -1 * d_d[i], -1 * d_f[i], cond_b[i]])
        return clauses
    @classmethod
    def build_operation_tree(cls, expression_list, var_num):
        operation_stack = []
        operand_stack = []
        for ch in expression_list:
            if cls.is_operand(ch, var_num):
                operand_stack.append(VarOperationNode(None, None, ch))
            elif cls.is_operation(ch):
                while operation_stack and cls.is_operation(operation_stack[-1]) and operationPrior[ch] <= operationPrior[operation_stack[-1]]:
                    operation_ch = operation_stack[-1]
                    operation_stack.pop()
                    if operation_ch == "~":
                        operand_1 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.append(NotOperationNode(operand_1, None))
                    elif operation_ch == "&":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(AndOperationNode(operand_1, operand_2))
                    elif operation_ch == "|":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(OrOperationNode(operand_1, operand_2))
                    elif operation_ch == "^":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(XOROperationNode(operand_1, operand_2))
                operation_stack.append(ch)
            elif ch == "(":
                operation_stack.append(ch)
            elif ch == ")":
                while operation_stack and operation_stack[-1] != "(":
                    operation_ch = operation_stack[-1]
                    operation_stack.pop()
                    if operation_ch == "~":
                        operand_1 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.append(NotOperationNode(operand_1, None))
                    elif operation_ch == "&":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(AndOperationNode(operand_1, operand_2))
                    elif operation_ch == "|":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(OrOperationNode(operand_1, operand_2))
                    elif operation_ch == "^":
                        operand_1 = operand_stack[-2]
                        operand_2 = operand_stack[-1]
                        operand_stack.pop()
                        operand_stack.pop()
                        operand_stack.append(XOROperationNode(operand_1, operand_2))
                if len(operation_stack) == 0 or operation_stack[-1] != "(":
                    raise_error("正在解析F函数定义 {}, 表达式解析错误!".format(concatenate_str_list(expression_list)))
                operation_stack.pop()
        if len(operation_stack) != 0 or len(operand_stack) != 1:
            raise_error("正在解析F函数定义 {}, 表达式解析错误!".format(concatenate_str_list(expression_list)))
        return operand_stack[0]

    def build_function_clauses_diff_real(self):
        allow_set = set()
        illegal_list = []
        for input_val in range(2**self.var_num):
            f_value = int(self.lookup_table[input_val])
            for diff_val in range(2**self.var_num):
                input_val2 = input_val ^ diff_val
                f_value2 = int(self.lookup_table[input_val2])
                f_diff_val = f_value ^ f_value2
                key = (diff_val << 1) | f_diff_val
                key = (key << self.var_num) | input_val
                key = (key << 1) | f_value
                allow_set.add(key)
        key_length = 2 * (self.var_num + 1)
        for key in range(2**key_length):
            if key not in allow_set:
                illegal_list.append(int_to_bits(key, key_length))
        # 生成espresso输入文件
        with open("espresso_input.in", mode="w", encoding="utf-8") as f:
            f.write(f".i {key_length}\n.o 1\n")
            f.write(".ilb")
            for i in reversed(range(key_length)):
                f.write(f" W{i}")
            f.write("\n.ob F\n")
            for illegal_assignment in illegal_list:
                for i in illegal_assignment:
                    f.write(str(i))
                f.write(" 1\n")
            f.write(".e")
        # 使用espresso分析，解析输出文件
        function_clauses = []
        res = subprocess.call(SAT_util.espresso_cmd + " .\\espresso_input.in > .\\espresso_output.out", env=SAT_util.env_para, shell=True)
        with open("espresso_output.out", mode="r", encoding="utf-8") as f:
            line = f.readline().split()
            while line[0] != ".p":
                line = f.readline().split()
            clause_number = int(line[1])
            for i in range(clause_number):
                line = f.readline().split()
                clause_str = line[0]
                assert len(clause_str) == key_length
                clause_val = []
                for ch in clause_str:
                    if ch == "1":
                        clause_val.append(-1)
                    elif ch == "0":
                        clause_val.append(1)
                    elif ch == "-":
                        clause_val.append(0)
                function_clauses.append(clause_val)
        # 删除输入输出文件
        os.system(SAT_util.del_cmd + " espresso_input.in")
        os.system(SAT_util.del_cmd + " espresso_output.out")
        self.function_clauses = function_clauses

    def build_function_clauses(self, search_type):
        assert search_type in ["diff", "linear"]
        input_space = 2**self.var_num
        output_space = 2
        AT = np.zeros((input_space, output_space), dtype=np.uint32)
        if search_type == "diff":
            for in_diff in range(input_space):
                for a in range(input_space):
                    b = a ^ in_diff
                    out_diff = self.lookup_table[a] ^ self.lookup_table[b]
                    AT[in_diff][out_diff] += 1
        else:
            input_val = np.arange(input_space, dtype=np.uint32)
            output_val = self.lookup_table[input_val]
            for in_mask in range(input_space):
                for out_mask in range(output_space):
                    AT[in_mask][out_mask] = 2 * abs(np.sum(inner_product(input_val, in_mask, self.var_num) == inner_product(output_val, out_mask, 1)) - (input_space / 2))
        p_min = input_space
        for row in AT:
            for i in row:
                if i > 0 and i < p_min:
                    p_min = i
        w_num = math.ceil(-1 * math.log2(p_min / input_space))
        # 生成非法赋值集
        key_length = self.var_num + 1 + w_num
        allow_set = set()
        illegal_list = []
        for in_val in range(input_space):
            for out_val in range(output_space):
                if AT[in_val][out_val] > 0:
                    p = math.ceil(-1 * math.log2(AT[in_val][out_val] / input_space))
                    key = (in_val << 1) | out_val
                    key <<= w_num
                    for i in range(p):
                        key |= 1 << i
                    allow_set.add(key)
        for key in range(2**key_length):
            if key not in allow_set:
                illegal_list.append(int_to_bits(key, key_length))
        # 生成espresso输入文件
        with open("espresso_input.in", mode="w", encoding="utf-8") as f:
            f.write(f".i {key_length}\n.o 1\n")
            f.write(".ilb")
            for i in reversed(range(self.var_num)):
                f.write(f" I{i}")
            for i in reversed(range(1)):
                f.write(f" O{i}")
            for i in reversed(range(w_num)):
                f.write(f" W{i}")
            f.write("\n.ob F\n")
            for illegal_assignment in illegal_list:
                for i in illegal_assignment:
                    f.write(str(i))
                f.write(" 1\n")
            f.write(".e")
        # 使用espresso分析，解析输出文件
        function_clauses = []
        res = subprocess.call(SAT_util.espresso_cmd + " espresso_input.in > espresso_output.out", env=SAT_util.env_para, shell=True)
        with open("espresso_output.out", mode="r", encoding="utf-8") as f:
            line = f.readline().split()
            while line[0] != ".p":
                line = f.readline().split()
            clause_number = int(line[1])
            for i in range(clause_number):
                line = f.readline().split()
                clause_str = line[0]
                assert len(clause_str) == key_length
                clause_val = []
                for ch in clause_str:
                    if ch == "1":
                        clause_val.append(-1)
                    elif ch == "0":
                        clause_val.append(1)
                    elif ch == "-":
                        clause_val.append(0)
                function_clauses.append(clause_val)
        # 删除输入输出文件
        os.system(SAT_util.del_cmd + " espresso_input.in")
        os.system(SAT_util.del_cmd + " espresso_output.out")
        if search_type == "diff":
            self.counter_var_length_diff = w_num
            self.function_clauses_diff = function_clauses
        else:
            self.counter_var_length_linear = w_num
            self.function_clauses_linear = function_clauses

    def execute(self, cur_var_number, parent_list, is_search_diff=True):
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("编号为{}的F函数操作中, 父节点{}与子节点状态大小不一致!".format(self.index, parent.index))
        assert len(parent_list) == self.var_num
        function_clauses = self.function_clauses_diff if is_search_diff else self.function_clauses_linear
        counter_var_length = self.counter_var_length_diff if is_search_diff else self.counter_var_length_linear
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        cur_var_number += self.size
        counter_variables = []
        clauses = []
        key_length = self.var_num + 1 + counter_var_length
        for bit_index in range(self.size):
            bit_counter_variables = [i for i in range(cur_var_number, cur_var_number + counter_var_length)]
            cur_var_number += counter_var_length
            counter_variables += bit_counter_variables
            X = [parent.variables[bit_index] for parent in parent_list] + [self.variables[bit_index]] + [i for i in reversed(bit_counter_variables)]
            for function_clause in function_clauses:
                clause = []
                for i in range(key_length):
                    if function_clause[i] == 1:
                        clause.append(X[i])
                    elif function_clause[i] == -1:
                        clause.append(-1 * X[i])
                clauses.append(clause)
        return cur_var_number, clauses, counter_variables

    def hash_execute(self, cur_var_number, parent_list, with_cond=False):
        for parent in parent_list:
            if parent.size != self.size:
                raise_error("编号为{}的F函数操作中, 父节点{}与子节点状态大小不一致!".format(self.index, parent.index))
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size * 2)]
        cur_var_number += 2 * self.size
        clauses = []
        for i in range(self.size):
            X = [parent.variables[i] for parent in parent_list] + [self.variables[i]] + [parent.variables[i + self.size] for parent in parent_list] + [self.variables[i + self.size]]
            for clause in self.function_clauses:
                tmp_clause = []
                for i in range(len(X)):
                    if clause[i] == 1:
                        tmp_clause.append(X[i])
                    elif clause[i] == -1:
                        tmp_clause.append(-1 * X[i])
                clauses.append(tmp_clause)
        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            clauses += hash_gen_mdiff_conds(self.variables, self.cond_vars)
            # 目前只支持IF函数和XOR函数添加条件
            if self.cond_f_kind == SupportedCondF.UNDEFINED:
                raise_error("哈希函数中的F函数不支持添加条件!")
            elif self.cond_f_kind == SupportedCondF.IF:
                clauses += self.apply_if_cond(parent_list[self.f_cond_permutation[0]].variables, parent_list[self.f_cond_permutation[1]].variables, parent_list[self.f_cond_permutation[2]].variables, self.variables, parent_list[self.f_cond_permutation[0]].cond_vars, parent_list[self.f_cond_permutation[1]].cond_vars, parent_list[self.f_cond_permutation[2]].cond_vars)
            elif self.cond_f_kind == SupportedCondF.XOR:
                clauses += self.apply_xor_cond(parent_list[0].variables, parent_list[1].variables, parent_list[2].variables, self.variables, parent_list[0].cond_vars, parent_list[1].cond_vars, parent_list[2].cond_vars)
        return cur_var_number, clauses, []
    
    def idc_execute(self, round_index):
        senlist = []
        modelsentence="ASSERT(i_{}_{}_{}_{} = (IF {} = {} THEN {} ELSE i_{}_{}_{}_{} ENDIF));\n"
        for bit_index in range(self.size):
            # 生成条件变量
            mixedcase = ["", ""]
            for parent_index in self.parent_index_list:
                for j in [0, 1]:
                    mixedcase[j] += "@i_{}_{}_{}_{}".format(j, bit_index, parent_index, round_index)
            for j in [0, 1]:
                mixedcase[j] = mixedcase[j][1:]
            for input_val in range(2**self.var_num):
                res_str = "0bin1" if self.lookup_table[input_val] == 1 else "0bin0"
                input_val_bits = int_to_bits(input_val, self.var_num, True)
                case_string = "0bin"
                for i in input_val_bits:
                    case_string += str(i)
                for j in [0, 1]:
                    senlist.append(modelsentence.format(j, bit_index, self.index, round_index, mixedcase[j], case_string, res_str, j, bit_index, self.index, round_index))
        return senlist
    
    def pass_state(self, input_list):
        for input in input_list:
            if len(input) != self.size:
                raise_error("编号为{}的F函数操作中, 父节点与子节点状态大小不一致!".format(self.index))
        assert len(input_list) == self.var_num
        output = []
        for bit_index in range(self.size):
            input_val_bits = [input[bit_index] for input in input_list]
            input_val = bits_to_int(input_val_bits, True)
            output_val = self.lookup_table[input_val]
            if isinstance(input_val, int):
                output_val = int(output_val)
            output.append(output_val)
        return output
    
class PNode(OperationNode):
    def __init__(self, index, parent_index, input_length, output_length, p_bit_out_to_in):
        super().__init__(index, output_length, "P")
        self.parent_index = parent_index
        self.input_length = input_length
        self.output_length = output_length
        self.bit_out_to_in = copy.deepcopy(p_bit_out_to_in)
    
    def execute(self, cur_var_number, parent):
        if parent.size != self.input_length:
            raise_error("在编号为{}的P置换操作中, 父节点{}状态大小与P置换定义中输入大小不一致!".format(self.index, parent.index))
        for i in range(self.output_length):
            self.variables.append(parent.variables[self.bit_out_to_in[i]])
        return cur_var_number, [], []
    
    def hash_execute(self, cur_var_number, parent, with_cond=False):
        if parent.size != self.input_length:
            raise_error("在编号为{}的P置换操作中, 父节点{}状态大小与P置换定义中输入大小不一致!".format(self.index, parent.index))
        self.variables = [parent.variables[self.bit_out_to_in[i]] for i in range(self.output_length)] + [parent.variables[parent.size + self.bit_out_to_in[i]] for i in range(self.output_length)]
        if with_cond:
            self.cond_vars = [parent.cond_vars[self.bit_out_to_in[i]] for i in range(self.output_length)]
        return cur_var_number, [], []
    
    def idc_execute(self,round_index):
        sen_list=[]
        for j in [0,1]:
            for i in range(self.input_length):
                sen_list.append("ASSERT(i_{}_{}_{}_{} = i_{}_{}_{}_{});\n".format(j,self.bit_out_to_in[i],self.parent_index,round_index,j,i,self.index,round_index))
        return sen_list
    
    # PNode返回input经过P置换后的结果
    def pass_state(self, input):
        return [input[self.bit_out_to_in[i]] for i in range(self.output_length)]
    
# 未验证正确性
class SubKeyNode(OperationNode):
    def __init__(self, index, size):
        super().__init__(index, size, "SUBKEY")

    def execute(self, cur_var_number, is_search_diff=True):
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        clauses = []
        if is_search_diff:
            for i in self.variables:
                clauses.append([-1 * i])
        return cur_var_number + self.size, clauses, []
    
    def idc_execute(self,round_index):
        senlist=[]
        for i in range(self.size):
            senlist.append("ASSERT(i_0_{}_{}_{} = i_1_{}_{}_{});\n".format(i,self.index,round_index,i,self.index,round_index))
        return senlist
    
    def pass_state(self, input):
        return input
    
class MessageNode(OperationNode):
    def __init__(self, index, size):
        super().__init__(index, size, "MESSAGE")
    
    def execute(self, cur_var_number, is_search_diff=True):
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size)]
        clauses = []
        if is_search_diff:
            for i in self.variables:
                clauses.append([-1 * i])
        return cur_var_number + self.size, clauses, []

    def hash_execute(self, cur_var_number, with_cond=False):
        self.variables = [i for i in range(cur_var_number, cur_var_number + self.size * 2)]
        cur_var_number += 2 * self.size
        clauses = []
        if with_cond:
            self.cond_vars = [i for i in range(cur_var_number, cur_var_number + self.size)]
            cur_var_number += self.size
            clauses += hash_gen_mdiff_conds(self.variables, self.cond_vars)
        return cur_var_number, clauses, []

    def pass_state(self, input):
        return input
    
class ImportNode(OperationNode):
    def __init__(self, index, size, round_index, index_in_round):
        super().__init__(index, size, "IMPORT")
        # round_index:
        # -2, pre_round
        # -1, post_round
        # >=0, 绝对轮次引用
        # <-2, 相对轮次引用，真正的轮数为r+round_index+2
        self.round_index = round_index
        self.index_in_round = index_in_round

    def hash_execute(self, cur_var_number, node, with_cond=False):
        if self.size != node.size:
            raise_error("编号为{}的IMPORT操作引用的节点状态大小与声明不一致!".format(self.index))
        self.variables = node.variables[:]
        if with_cond:
            self.cond_vars = node.cond_vars[:]
        return cur_var_number, [], []
    
    def pass_state(self, input):
        return input
    
class ImportMNode(OperationNode):
    def __init__(self, index, size, target_message_index, is_main_message):
        super().__init__(index, size, "IMPORTM/IMPORTK")
        # target_message_index为字符串, 可表示数字, 也可以@开头引用一个可变常量
        self.target_message_index = target_message_index
        self.is_main_message = is_main_message

class HeadImportNode(OperationNode):
    def __init__(self, index, size, index_in_round):
        super().__init__(index, size, "HEAD_IMPORT")
        self.index_in_round = index_in_round

    def execute(self, cur_var_number, node):
        if self.size != node.size:
            raise_error("编号为{}的HEAD_IMPORT操作引用的节点状态大小与声明不一致!".format(self.index))
        self.variables = node.variables[:]
        return cur_var_number, [], []
    
class TailImportNode(OperationNode):
    def __init__(self, index, size, index_in_round):
        super().__init__(index, size, "TAIL_IMPORT")
        self.index_in_round = index_in_round

    def execute(self, cur_var_number, node):
        if self.size != node.size:
            raise_error("编号为{}的TAIL_IMPORT操作引用的节点状态大小与声明不一致!".format(self.index))
        self.variables = node.variables[:]
        return cur_var_number, [], []
    
class VarRotationNode(OperationNode):
    def __init__(self, index, size, case_size, case_index, parent_index, category="l"):
        super().__init__(index, size, "VROTATION")
        self.case_size = case_size
        self.case_index = case_index
        self.parent_index = parent_index
        self.category = category
        if 2**case_size != size:
            raise_error("正在解析编号为{}的VROTATION操作, 移位结果状态大小(size={})应等于移位数节点{}大小(size={})的二次幂!".format(self.index, size, self.case_index, self.case_size))

    def idc_execute(self, round_index):
        senlist = []
        mixedcase1=""
        mixedcase0=""
        for i in range(self.case_size):
            mixedcase1="@i_{}_{}_{}_{}".format(1,i,self.case_index,round_index)+mixedcase1
            mixedcase0="@i_{}_{}_{}_{}".format(0,i,self.case_index,round_index)+mixedcase0
        mixedcase0=mixedcase0[1:]
        mixedcase1=mixedcase1[1:]
        mixedcase=[mixedcase0,mixedcase1]
        modelsentence="ASSERT(i_{}_{}_{}_{} = (IF {} = {} THEN i_{}_{}_{}_{} ELSE i_{}_{}_{}_{} ENDIF));\n"
        for shift_num in range(2**self.case_size):
            shift_num_bits = int_to_bits(shift_num, self.case_size)
            case_string = "0bin"
            for i in shift_num_bits:
                case_string += str(i)
            if self.category == "l":
                # 循环左移
                this_to_parent_index = [(i + self.size - shift_num) % self.size for i in range(self.size)]
            else:
                # 循环右移
                this_to_parent_index = [(i + self.size + shift_num) % self.size for i in range(self.size)]
            for j in [0, 1]:
                for i in range(self.size):
                    senlist.append(modelsentence.format(j, i, self.index, round_index, mixedcase[j], case_string, j, this_to_parent_index[i], self.parent_index, round_index, j, i, self.index, round_index))
        return senlist
    
    def pass_state(self, input_value, input_case):
        if len(input_value) != self.size:
            raise_error("正在执行编号为{}的VROTATION节点, 父节点大小({})与子节点大小({})不一致!".format(len(input_value), self.size))
        if len(input_case) != self.case_size:
            raise_error("正在执行编号为{}的VROTATION节点, 条件节点大小({})与算法定义中({})不一致!".format(len(input_case), self.case_size))
        shift_num = bits_to_int(input_case, False)
        if isinstance(input_value[0], np.ndarray):
            # 输入状态为数组形式
            n = len(input_value[0])
            input_value = np.array(input_value, dtype=np.uint8)
            this_to_parent_index = np.arange(self.size, dtype=np.uint32).reshape(-1, 1).repeat(n, axis=1)
            if self.category == "l":
                this_to_parent_index = (this_to_parent_index + self.size - shift_num) % self.size
            else:
                this_to_parent_index = (this_to_parent_index + self.size + shift_num) % self.size
            column_index = np.arange(n, dtype=np.uint32).reshape(1, -1).repeat(self.size, axis=0)
            output = input_value[this_to_parent_index, column_index]
        else:
            # 输入单个样本
            if self.category == "l":
                this_to_parent_index = [(i + self.size - shift_num) % self.size for i in range(self.size)]
            else:
                this_to_parent_index = [(i + self.size + shift_num) % self.size for i in range(self.size)]
            output = []
            for i in range(self.size):
                output[i] = input_value[this_to_parent_index[i]]
        return output