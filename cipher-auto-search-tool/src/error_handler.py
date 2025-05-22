import sys

def raise_error(error_info):
    print("\n运行错误! " + error_info)
    sys.exit()

def raise_node_error(node_index, loop_index, error_info):
    if loop_index == -2:
        location_info = "轮函数前"
    elif loop_index == -1:
        location_info = "轮函数后"
    else:
        location_info = str(loop_index)
    print("\n运行错误! " + error_info + " 错误节点位置在第{}个循环体, 编号为{}.".format(location_info, node_index))
    sys.exit()