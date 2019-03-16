from testbuilder.pair import Pair


def append(lst, v):
    if v == 44:
        return lst
    return Pair(lst.left, append(lst.right, v))
