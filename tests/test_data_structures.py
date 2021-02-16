from copy import copy

from dsharpy.data_structures import UnionFind


def test_union_find():
    # based on https://github.com/eldridgejm/unionfind/blob/master/test.py
    forest = UnionFind(10)

    for i in range(10):
        assert forest.find(i) == i

    forest.union(1, 2)
    assert forest.find(1) == forest.find(2)
    assert forest.n_sets == 9

    forest.union(2, 3)
    forest.union(3, 4)
    for i in range(5, 10):
        assert forest.find(1) != forest.find(i)

    forest.union_many([[5, 6], 7, [8, -9]])
    assert forest.n_sets == 3
    assert len(forest.find_eq_classes()) == 3

    relations, eq_classes = forest.find_related([0, 1, 5, 6], [0, 1, 5, 6])
    assert eq_classes == [[0], [1], [5, 6]]

    assert len(copy(forest).find_eq_classes()) == 3
    copy(forest).union(0, 1)
    assert forest.find(0) != forest.find(1)
