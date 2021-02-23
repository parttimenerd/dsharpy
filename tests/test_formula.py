import math

import pytest

from dsharpy.formula import RangeSplitXORGenerator, FullyRandomXORGenerator, XOR, XORs, blast_xor, \
    IncrementalRelations, Dep, DCNF, trim_dcnf
from pysat.formula import CNF


def test_xor_reduce_variability_by_one_ranged():
    generator = RangeSplitXORGenerator()
    vars = [1, 2, 3, 4, 5, 6]
    xors = generator.generate(vars, len(vars) - 1)
    print(xors)
    assert math.log2(xors.count_sat()) == len(vars) - 1


def test_xor_reduce_variability_by_one_fully():
    generator = FullyRandomXORGenerator()
    vars = [1, 2, 3, 4, 5, 6]
    xors = generator.generate(vars, len(vars) - 1)
    print(xors)
    assert math.log2(xors.count_sat(vars)) == len(vars) - 1


def test_blast_xor_sat():
    vars = [1, -2, 3, -4, 5]
    for i in range(2, 5):
        xor = XOR(vars[:i])
        print(xor)
        print(xor.to_dimacs(10))
        assert XORs([xor]).count_sat() > 1.0, xor


def test_blast_single_xor():
    res = blast_xor([1, 2], new_start=0)
    assert [-1, -2] in res
    assert [1, 2] in res
    assert len(res) == 2


@pytest.mark.parametrize('count', range(1, 10))
def test_blast_xor_count(count: int):
    """
    Test that the number of solutions for an xor expression with
    $count$ variables is $2^(count - 1)$.
    This is a fundamental fact abort xors and should also hold for
    the xor blasted into CNF
    """
    xor = XOR(list(range(1, count + 1)))
    print(xor)
    print(xor.to_dimacs(100))
    assert math.log2(xor.count_sat()) == count - 1


def test_range_split_with_more_variability_than_variables():
    xor = FullyRandomXORGenerator().generate([1, 2], 5)
    assert xor == XORs([])


def test_incremental_relations():

    inc = IncrementalRelations.create(CNF(from_clauses=[
        [1, 2],
        [2, 3],
        [5, 6]
    ]), [1], [6])
    rels, eqs = inc.compute([Dep({3}, {5})])
    assert rels[1] == [6]


def test_trim_with_misc_ind_var():
    cnf = DCNF().set_ind({1})
    assert trim_dcnf(cnf).nv == 1
    assert cnf.comments == ["c ind 1 0"]
