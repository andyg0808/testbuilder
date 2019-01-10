def basic_pair_use(first, a):
    if first == 0 and a.left == 1:
        a.left = a.left + 32
        return a.left
    else:
        return 5


def simple_inferred_pair(a):
    a.left += 32
    return a
