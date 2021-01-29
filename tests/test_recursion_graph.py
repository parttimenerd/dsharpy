import pytest
from pytest_check import check

from dsharpy.formula import Dep
from dsharpy.recursion_graph import ApplicableCNF, NameMapping, Variable, parse_variable, transpose_clauses, \
    transpose_dep


@pytest.mark.parametrize("string,expected",
                         [("True", True), ("TRUE", True), ("1", 1), ("-1", -1)])
def test_parse_variable(string: str, expected: Variable):
    assert parse_variable(string) == expected


def test_transpose_clauses():
    mapping = {1: True, 2: 3, 3: False}
    assert transpose_clauses([[1], [2]], mapping) == [[3]]  # True removes the clause
    assert transpose_clauses([[3], [2]], mapping) == [[]]  # False empties the clause and removes all others


def test_transpose_dep():
    mapping = {1: True, 2: 3, 3: False}
    with check():
        dep = Dep(frozenset({1, 2, 3}), frozenset({1, 2, 3}))
        assert transpose_dep(dep, mapping) == Dep(frozenset({3}), frozenset({3}))
    with check():
        dep = Dep(dep.param, dep.ret, constraint=frozenset({1}))  # constraint is True  → omit True
        assert transpose_dep(dep, mapping) == Dep(frozenset({3}), frozenset({3}))
    with check():
        dep = Dep(dep.param, dep.ret, constraint=frozenset({3}))  # constraint is False → dismiss dep
        assert not transpose_dep(dep, mapping)


class TestNameMapping:

    def test_transpose(self):
        mapping = NameMapping({"input": [1, 2]})
        assert mapping.transpose({1: True, 2: 3}) == NameMapping({"input": [True, 3]})


class TestApplicableCNF:
    app = ApplicableCNF(input=NameMapping({"in": [1, 2]}),
                        output=NameMapping({"out": [5, 6]}),
                        clauses=[[1, 3], [3, 5, 6]],
                        deps=[],
                        misc_vars=NameMapping({"misc": [3]}))

    def test_incompatible_mapping(self):
        with pytest.raises(AssertionError):
            self.app.apply(1, NameMapping({"in": [7, 8, 9]}), None)

    def test_transpose(self):
        res = self.app.transpose(10, keep=[1, 2], custom_mapping={})
        assert res.input == self.app.input
        assert res.output["out"] == [11, 12]
        assert res.clauses == [[1, 10], [10, 11, 12]]
        assert res.misc_vars["misc"] == [10]

    def test_apply(self):
        res = self.app.apply(10, NameMapping({"in": [7, 8]}), output=None)
        assert res.output["out"] == [11, 12]
        assert res.input["in"] == [7, 8]
