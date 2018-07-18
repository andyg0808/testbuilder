import operator as op
from functools import partial
from unicodedata import normalize

from hypothesis.strategies import characters, integers, one_of, sampled_from, text

function_names = text(
    characters(whitelist_categories=["Lu", "Ll", "Lt"]), min_size=1
).map(partial(normalize, "NFKC"))

functions = sampled_from([max, min, op.add, op.sub, op.mul, op.floordiv, op.truediv])
