import pytest
from pytest_check import check

from dsharpy.formula import Dep
from dsharpy.recursion_graph import ApplicableCNF, NameMapping, Variable, parse_variable, transpose_clauses, \
    transpose_dep, RecursionNode, RecursionChild, RecursionProcessingResult
from dsharpy.util import single


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


def test_abstract_rec_to_applicable():
    """
    See test_fib_with_abstract_rec() for origin

    rec_child is an application of rec_node, this test case tests that the dependency produced by rec_child is correct
    """

    # setup code to match roughly the situation
    node_store = {}
    rec_node = RecursionNode("fib(char)",
                             ApplicableCNF(input=NameMapping(base={'fib(char)::num': [82, 83]}),
                                           output=NameMapping(base={
                                               'fib(char)#return_value': [166, 167]}),
                                           clauses=[[-84, -90], [-83, 84, -90], [89, -119, -120],
                                                    [-89, 119, -120], [89, 119, 120], [-2, -165, 173]], deps=[],
                                           misc_vars=NameMapping(base={})),
                             [RecursionChild(node_store=node_store, id=0, node_id='fib(char)', input=NameMapping(
                                 base={'fib(char)::num': [82, 83]}), output=NameMapping(
                                 base={'fib(char)#return_value': [158, 159]}),
                                             constraint={2})])
    node_store[rec_node.id] = rec_node
    proc_res = RecursionProcessingResult(max_variability={rec_node: 9})
    rec_child = RecursionChild(node_store={'fib(char)': rec_node}, id=1, node_id='fib(char)',
                               input=NameMapping(base={'fib(char)::num': [6, 7]}),
                               output=NameMapping(
                                   base={'fib(char)#return_value': [174, 175]}),
                               constraint={1})

    dep, clauses = proc_res.to_dep(rec_child, 1000)
    # no constraints are specified
    assert not clauses

    # param and ret have to be equivalent
    assert dep.param == frozenset(single(rec_child.input))
    assert dep.ret == frozenset(single(rec_child.output))

    # this holds also true for the constraints
    assert dep.constraint == frozenset(rec_child.constraint)
    # and the max_variability has to be as set in proc_res
    assert dep.max_variability == proc_res.max_variability[rec_node]
