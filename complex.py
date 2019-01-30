def mult(i, j):
    return i * j


def print_all(count):
    while count > 0:
        count -= 1
        print(count)


def run_them():
    print_all(mult(2, 3))
