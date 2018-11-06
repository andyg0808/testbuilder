from hypothesis import given
from hypothesis.strategies import integers, none, one_of, text
from toolz import pipe

from .iter_monad import bind, chain, liftIter, optional_to_iter, returnIter

extract = next


@given(text())
def test_extract_from_iter(s):
    assert next(returnIter(s)) == s


@given(integers())
def test_lift_iter(k):
    lifted = liftIter(lambda i: i + 1)
    item = pipe(k, returnIter, lifted, extract)
    assert item == k + 1


@given(text())
def test_lift_iter_string(s):
    lifted = liftIter(reversed)
    item = pipe(s, returnIter, lifted, extract)
    assert list(item) == list(reversed(s))


@given(integers(max_value=1500))
def test_bind_functions(k):
    data = returnIter(k)
    res = bind(data, range)
    assert list(res) == [i for i in range(k)]


@given(integers(max_value=1500))
def test_chain_functions(k):
    def funny_func(i):
        yield i
        yield i + 1

    data = returnIter(k)
    res = chain(range, funny_func)(data)

    expected = [i for i in range(k)] + [i for i in range(k + 1)]

    assert list(res) == expected


@given(one_of(text(), none()))
def test_optional_to_iter(s):
    res = optional_to_iter(s)
    if s is None:
        assert list(res) == []
    else:
        assert list(res) == [s]
