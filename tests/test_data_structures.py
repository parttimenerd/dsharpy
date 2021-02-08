from array import array

from dsharpy.data_structures import UnionFind

# based on https://github.com/eldridgejm/unionfind/blob/master/test.py

def test_basic():
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

    forest.union_many([5, 6, 7, 8, 9])
    forest.n_sets == 3
    assert len(forest.eq_classes) == 3
