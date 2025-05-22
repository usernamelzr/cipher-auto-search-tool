def sequential_encoding(cur_var_number, counter_variables, upper_bound):
    assert upper_bound >= 0
    clauses = []
    # 特判：上界等于0，即所有变量全部为0
    if upper_bound == 0:
        for i in counter_variables:
            clauses.append([-1 * i])
        return cur_var_number, clauses, []
    n = len(counter_variables)
    # 特判：计数变量为1
    if n <= 1:
        return cur_var_number, clauses, []
    s = []
    for i in range(n - 1):
        s.append([j for j in range(cur_var_number, cur_var_number + upper_bound)])
        cur_var_number += upper_bound
    clauses.append([-1 * counter_variables[0], s[0][0]])
    for j in range(1, upper_bound):
        clauses.append([-1 * s[0][j]])
    for i in range(1, n - 1):
        clauses.append([-1 * counter_variables[i], s[i][0]])
        clauses.append([-1 * s[i-1][0], s[i][0]])
        for j in range(1, upper_bound):
            clauses.append([-1 * counter_variables[i], -1 * s[i-1][j-1], s[i][j]])
            clauses.append([-1 * s[i-1][j], s[i][j]])
        clauses.append([-1 * counter_variables[i], -1 * s[i-1][upper_bound-1]])
    clauses.append([-1 * counter_variables[n-1], -1 * s[n-2][upper_bound-1]])
    return cur_var_number, clauses, s

def add_bounding_condition(l, r, k, m, counter_variables, s):
    assert l <= r
    assert m <= k and m >= 0
    n = len(counter_variables)
    clauses = []
    # 特判m等于0
    if m == 0:
        for i in range(l, r + 1):
            clauses.append([-1 * counter_variables[i]])
        return clauses
    if l == 0 and r < n - 1:
        for i in range(1, r + 1):
            clauses.append([-1 * counter_variables[i], -1 * s[i-1][m-1]])
    elif l > 0 and r < n - 1:
        for i in range(0, k - m):
            clauses.append([s[l-1][i], -1 * s[r][i+m]])
    else:
        for i in range(0, k - m):
            clauses.append([s[l-1][i], -1 * s[n-2][i+m]])
        for i in range(0, k - m + 1):
            clauses.append([s[l-1][i], -1 * counter_variables[n-1], -1 * s[n-2][i+m-1]])
    return clauses

def add_suffix_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound):
    assert round_number == len(counter_variables_per_round)
    clauses = []
    n = len(counter_variables)
    # 特判：确定性模型不需要加定界条件
    if n == 0:
        return clauses
    # 添加条件C(*,R-1)
    r = n - 1
    l = n
    for r1 in range(round_number - 1, 0, -1):
        l -= len(counter_variables_per_round[r1])
        m = counter_upper_bound - his_counter_upper_bound[r1]
        clauses += add_bounding_condition(l, r, counter_upper_bound, m, counter_variables, s)
    return clauses

def add_prefix_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound):
    assert round_number == len(counter_variables_per_round)
    clauses = []
    n = len(counter_variables)
    # 特判：确定性模型不需要加定界条件
    if n == 0:
        return clauses
    # 添加条件C(0,*)
    l = 0
    r = -1
    for r2 in range(round_number - 1):
        r += len(counter_variables_per_round[r2])
        m = counter_upper_bound - his_counter_upper_bound[round_number - r2 - 1]
        clauses += add_bounding_condition(l, r, counter_upper_bound, m, counter_variables, s)
    return clauses

def add_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound, prefix_bounding=True, suffix_bounding=True):
    assert round_number == len(counter_variables_per_round)
    clauses = []
    n = len(counter_variables)
    # 特判：确定性模型不需要加定界条件
    if n == 0:
        return clauses
    # 添加前缀变量条件
    if prefix_bounding:
        clauses += add_prefix_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound)
    # 添加后缀变量条件
    if suffix_bounding:
        clauses += add_suffix_bounding_conditions(round_number, counter_variables, counter_variables_per_round, s, counter_upper_bound, his_counter_upper_bound)
    return clauses