import math
import statistics
from pathlib import Path
from pytest_check import check

import numpy
import pytest
from pysat.formula import CNF

from dsharpy.counter import State, Config
from dsharpy.formula import sat, DCNF, count_sat, blast_xor
from dsharpy.util import random_seed, process_code_with_cbmc, to_bit_ceil
from tests.util import load


def test_sat():
    assert sat(CNF(from_clauses=[[1]]))
    assert not sat(CNF(from_clauses=[[1], [-1]]))


def test_dcnf_loading():
    assert load("test1.cnf").ind == {1, 2}


def test_dncf_counting():
    """ Count the models of a small CNF using ApproxMC """
    cnf = load("test1.cnf")
    assert count_sat(cnf) == 3


def test_count_multiple():
    """ Count the models of multiple formulas """
    assert len(count_sat([load("test1.cnf"), load("test2.cnf")])) == 2


BASIC_PROGRAM = """
p cnf 0 2
1 2 0 
3 4 0
c ind 4 0
c dep 2 0 3
"""


def test_split_and_more():
    state = State.from_string(BASIC_PROGRAM)
    dep, cnf, new_state = state.split()
    assert dep == ({2}, {3})
    assert cnf.clauses == [[1, 2]]
    assert "c ind 2 0" in cnf.comments and len(cnf.comments) == 1
    assert not new_state.can_split()
    assert "c ind 4 0" in new_state.cnf.comments
    assert new_state.cnf.clauses == [[3, 4]]
    assert state._count_sat(cnf) == 2


def test_xor_generation():
    state = State.from_string(BASIC_PROGRAM)
    dep, cnf, new_state = state.split()
    assert state.create_random_xor_clauses(dep[1], 1) == []  # one variable has one bit of variability
    assert len(state.create_random_xor_clauses(dep[1], 0)) in [0, 1]


def test_basic_program_computation():
    state = State.from_string(BASIC_PROGRAM)
    assert state.compute() == 2


def test_basic_program2_computation():
    state = State.from_string("""
p cnf 0 2
c ind 2 3 0
c dep 1 0 2 3
""")
    arr = [state.compute() for i in range(20)]
    print(arr)
    assert numpy.mean(arr) >= 2
    assert numpy.median(arr) == 2


def test_blast_xor():
    assert blast_xor(3) == [[3]]


def test_basic_compute():
    string = """
p cnf 0 2
1 2 0
c ind 1 2 0
c dep 2 0 1
"""
    random_seed(10)
    val = State.from_string(string).compute()
    assert val == 3


@pytest.mark.skip("I'm unsure what this program should leak")
def test_recursive_code_unsure():
    string = process_code_with_cbmc("""
    #include <assert.h>
    char non_det_char();
    char non_det_char2();
char fib(char num){
  if (num > 2)
  {
    return fib(num) + 1;
  }
  return num;
}

void main()
{
  char b = fib(non_det_char2());
  char __out = b;
  assert(non_det_char());
}
""", preprocess=False)
    state = State.from_string(string)
    (a_s, bs), cnf, new_state = state.split()
    for i in a_s:
        _cnf = CNF()
        print(f"variability({i}) = {state.count_sat(cnf, ind={i})}")
    available_variability = state._count_sat(cnf)
    assert available_variability == 130  # 2 < num <= 127 # I don't know why it isn't 131

    assert state.count_sat(state.cnf, ind=bs) == 256, "variability of bs"

    ov_possible_variability = state.count_sat(cnf, ind=state.cnf.ind)
    with check():
        assert ov_possible_variability == 256, "ov_possible_variability"

    val = State.from_string(string).compute()
    assert val == 256


def test_recursive_code():
    string = process_code_with_cbmc("""
    #include <assert.h>
    char non_det_char();
    char non_det_char2();
char fib(char num){
  if (num > 2)
  {
    return fib(num + 1) + 1;
  }
  return num;
}

void main()
{
  char b = fib(non_det_char2());
  char __out = b;
  assert(non_det_char());
}
""", preprocess=False)
    state = State.from_string(string)
    (a_s, bs), cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 134  # 2 < num <= 127 # I don't know why it isn't 131
    val = State.from_string(string).compute()
    assert val == 256


def test_recursive_code_real_fib():
    string = process_code_with_cbmc("""
    char non_det_char();
    char non_det_char2();
char fib(char num){
  if (num <= 0){
    return 0;
  }
  if (num > 2)
  {
    return fib(num - 1) + fib(num - 2);
  }
  return num;
}

void main()
{
  char b = fib(non_det_char2());
  char __out = b;
  assert(non_det_char());
}
""", preprocess=True, unwind=2)
    val = State.from_string(string).compute()
    assert val == 256


def _id_fn(file: Path) -> str:
    return str(file)


class TestFile:

    def test_test0(self):
        self.check_case("test0.cnf")

    def test_test1(self):
        self.check_case("test1.cnf")

    def test_test5(self):
        self.check_case("test5.cnf")

    def test_indies(self):
        self.check_case("test1b_indies.cnf")

    def test_test1b_in_parallel(self):
        self.check_case("test1b.cnf", Config(parallelism=2))

    def test_test1b(self):
        l = [State(load("test1b.cnf")).compute() for i in range(10)]
        for i in range(math.floor(min(l)), math.ceil(max(l)) + 1):
            print(f"{i}: {sum([1 for x in l if x == i])}")
        print(statistics.quantiles(l, n=10))

    @pytest.mark.parametrize(
        'file', sorted(f for f in Path("cases").glob("*.cnf")),
        ids=_id_fn
    )
    def test_small_files(self, file: Path):
        self.check_file(file)

    @pytest.mark.parametrize(
        'file', sorted(f for f in Path("cases").glob("*.cnf")),
        ids=_id_fn
    )
    # @pytest.mark.skip()
    def test_small_files_multiple_times(self, file: Path):
        for i in range(5):
            self.check_file(file)

    @pytest.mark.parametrize(
        'file', sorted(f for f in Path("cases/large").glob("*.cnf")),
        ids=_id_fn
    )
    def test_large_files(self, file: Path):
        self.check_file(file)

    @staticmethod
    def check_case(name: str, config: Config = None):
        TestFile.check_file(Path("cases") / name, config)

    @staticmethod
    def check_file(file: Path, config: Config = None):
        cnf = DCNF.load(file)
        actual = State(cnf, config).compute_loop(1)
        if exp_comment := cnf.get_comment("test count"):
            expected = eval(exp_comment.split(" ")[-1])
            assert actual == expected
        else:
            expected = count_sat(cnf)
            if expected is None:
                assert actual is None
            else:
                assert actual is not None and actual <= expected
