from testbuilder.pair import Pair


def append(lst, v):
    return Pair(lst.left, append(lst.right, v))
