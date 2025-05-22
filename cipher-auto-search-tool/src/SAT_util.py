from error_handler import raise_error
import os

file_path_separator = "/"

SAT_tmp_folder = "./SAT_tmp/"
CaDiCaL_cmd = "./bin/cadical"
espresso_cmd = "./bin/espresso"
stp_cmd = "./bin/stp"
library_path = "./bin/lib"
env_para = {}
del_cmd = "rm"

search_result_folder = "search_res/"

# system_type: windows or linux
def set_cmd_str(system_type):
    global file_path_separator, SAT_tmp_folder, CaDiCaL_cmd, espresso_cmd, stp_cmd, library_path, env_para, del_cmd
    if system_type == "windows":
        file_path_separator = "\\"
        del_cmd = "del"
    elif system_type == "linux":
        file_path_separator = "/"
        del_cmd = "rm"
    else:
        raise_error("未识别的系统配置: {}".format(system_type))
    
    SAT_tmp_folder = ".{0}SAT_tmp{0}".format(file_path_separator)
    CaDiCaL_cmd = ".{0}bin{0}cadical".format(file_path_separator)
    espresso_cmd = ".{0}bin{0}espresso".format(file_path_separator)
    stp_cmd = ".{0}bin{0}stp".format(file_path_separator)
    library_path = ".{0}bin{0}lib".format(file_path_separator)
    env_para = os.environ.copy()
    env_para["PATH"] = env_para["PATH"] + ";" + library_path

    if system_type == "windows":
        CaDiCaL_cmd += ".exe"
        espresso_cmd += ".exe"
        stp_cmd += ".exe"

def set_search_result_folder(folder: str):
    global search_result_folder
    search_result_folder = folder
    if (not folder.endswith("/")) and (not folder.endswith("\\")):
        search_result_folder += file_path_separator

def search_res_path(cipher_name, search_type, whether_consider_pr=True):
    global search_result_folder
    if search_type == "diff_linear":
        search_type = "dl"
    elif search_type == "real":
        search_type = "idc"
    elif search_type == "diff_real":
        search_type = "hash"
    elif search_type == "diff":
        if not whether_consider_pr:
            search_type = "diff_activeSBox"
    elif search_type == "linear":
        if not whether_consider_pr:
            search_type = "linear_activeSBox"
    return search_result_folder + cipher_name + "_" + search_type + "_res.txt"

# 由变量子句列表clauses构造DIMACS格式SAT求解器输入文件
def construct_dimacs_input(file_path, clauses, var_number):
    f = open(file_path, mode="w", encoding="utf-8")
    f.write(f"p cnf {var_number} {len(clauses)}\n")
    for clause in clauses:
        assert len(clause) > 0
        for v in clause:
            f.write(f"{v} ")
        f.write("0\n")
    f.close()

# 由SAT求解器输出文件file_path解析出每个变量的取值
# 若UNSAT, 返回空列表
def get_var_solution(file_path):
    var_solution = [-1]
    with open(file_path, mode="r", encoding="utf-8") as f:
        while True:
            line = f.readline().split()
            if line[0] == "s":
                break
        if line[1] == "SATISFIABLE":
            line = f.readline().split()
            assert line[0] == "v"
            while line[0] == "v":
                for i in line[1:]:
                    if int(i) == 0:
                        break
                    assert abs(int(i)) == len(var_solution)
                    if int(i) < 0:
                        var_solution.append(0)
                    else:
                        var_solution.append(1)
                line = f.readline().split()
    if len(var_solution) == 1:
        return []
    else:
        return var_solution