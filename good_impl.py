from testbuilder.pair import Pair


def append(lst, v):
    if isinstance(lst, Pair):
        return Pair(lst.left, append(lst.right, v))
    else:
        assert lst is None
        return Pair(v, lst)
