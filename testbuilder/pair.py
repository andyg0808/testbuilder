class Pair:
    def __init__(self, left, right):  # type: ignore
        self.left = left
        self.right = right

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Pair):
            return False
        l_eq = self.left == other.left
        r_eq = self.right == other.right
        return bool(l_eq and r_eq)

    def __repr__(self) -> str:
        return "Pair(" + str(self.left) + ", " + str(self.right) + ")"
