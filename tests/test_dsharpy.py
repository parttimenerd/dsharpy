import math
import statistics
from pathlib import Path
from typing import Tuple

import numpy
import pytest
from pysat.formula import CNF
from pytest_check import check

from dsharpy.convert import Graph
from dsharpy.counter import State, Config
from dsharpy.formula import sat, DCNF, count_sat, Dep, RangeSplitXORGenerator
from dsharpy.util import random_seed, process_code_with_cbmc, process_code_with_jbmc, CBMCOptions, single
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
    assert dep == Dep(frozenset([2]), frozenset([3]))
    assert cnf.clauses == [[1, 2]]
    assert "c ind 2 0" in cnf.comments and len(cnf.comments) == 1
    assert not new_state.can_split()
    assert "c ind 4 0" in new_state.cnf.comments
    assert new_state.cnf.clauses == [[3, 4]]
    assert state._count_sat(cnf) == 2


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


def test_basic_compute_with_max_variability():
    string = """
p cnf 0 2
1 2 0
c ind 1 2 4 0
c dep 2 3 0 1 4 0 0 1 0
"""
    random_seed(10)
    val = State.from_string(string).compute()
    assert val == 2


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
""", CBMCOptions(preprocess=False))
    state = State.from_string(string)
    dep, cnf, new_state = state.split()
    for i in dep.param:
        _cnf = CNF()
        print(f"variability({i}) = {state.count_sat(cnf, ind={i})}")
    available_variability = state._count_sat(cnf)
    assert available_variability == 126  # 2 < num <= 127 # I don't know why it isn't 131

    assert state.count_sat(state.cnf, ind=dep.ret) == 256, "variability of bs"

    ov_possible_variability = state.count_sat(cnf, ind=state.cnf.ind)
    with check():
        assert ov_possible_variability == 256, "ov_possible_variability"

    val = State.from_string(string,
                            Config(xor_generator=RangeSplitXORGenerator(), amc_epsilon=0.01, amc_delta=0.01)).compute()
    assert val > 240  # maybe?


def test_recursive_code_reduced_with_guard():
    string = process_code_with_cbmc("""
    #include <assert.h>
bool fib(bool num){
  if (num)
  {
    return fib(num); // the variability of num should only be 1 
  }
  return num;
}

void main()
{
  bool __out = fib(non_det_bool()); 
  // but the overall variability of the program should be 2
  // as it is unknown what fib(num) does
  END;
}
""", CBMCOptions(rec=0))
    state = State.from_string(string, Config(xor_generator=RangeSplitXORGenerator()))
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 1
    val = state.compute()
    assert val == 2
    print(val)


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
""", CBMCOptions(rec=0, preprocess=False))
    state = State.from_string(string, Config(amc_epsilon=0.1))
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 125
    assert state.compute() >= 131


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
""", CBMCOptions(unwind=3, rec=1))
    val = State.from_string(string, Config(check_xors_for_variability=False)).compute()
    assert val == 256


def test_small_loop():
    string = process_code_with_cbmc("""
char non_det_char();
char non_det_char2();

void main()
{
  char num = non_det_char2();
  char res = 0;
  while (res < num) {
    res += 1;
  }
  char __out = res;
  assert(non_det_char());
}
""", CBMCOptions(unwind=3))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 128  # cannot count the first round, discard the next two? todo: correct?
    assert state.compute() == 256


def test_small_loop_reduced():
    string = process_code_with_cbmc("""
char non_det_char();
char non_det_char2();

void main()
{
  char num = non_det_char2();
  char res = 1;
  while (res != num) {
    res = res << 2;
  }
  char __out = res;
  assert(non_det_char());
}
""", CBMCOptions(unwind=3))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 256
    assert state.compute() == 256


def test_small_loop2():
    string = process_code_with_cbmc("""
char non_det_char();
char non_det_char2();

void main()
{
  char num = non_det_char2();
  char res = 1;
  while (res < num) {
    res *= 4;
    num *= 2;
  }
  char __out = res;
  assert(non_det_char());
}
""")
    state = State.from_string(string, config=Config(xor_generator=RangeSplitXORGenerator()))
    assert len(state.cnf.deps) == 1
    dep, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 126
    av_bits = math.ceil(math.log2(available_variability))
    assert av_bits == 7
    xors = state.create_random_xor_clauses(dep.ret, av_bits)
    print(f"constraints: {xors}")
    print(xors.count_sat())
    assert state.compute() == 256


def test_small_loop3():
    string = process_code_with_cbmc("""
char non_det_char();
char non_det_char2();

void main()
{
  char num = non_det_char2();
  char res = 1;
  while (res < num) {
    res *= 4;
    num++;
    num *= res == 2 ? 3 : 1;
  }
  char __out = res;
  assert(non_det_char());
}
""")
    val = State.from_string(string).compute()
    assert val == 256


def test_array_in_loop():
    string = process_code_with_cbmc("""
    void main()
    {
      int arr[10];
      int S = non_det();
      for (int i = 0; i < 10; i++){
        arr[i] = S & i;
      }
      int __out = arr[4];
      END;
    }
    """, CBMCOptions(unwind=5))
    val = math.log2(State.from_string(string).compute())
    assert val == 32


def test_global_variables_with_recursion():
    string = process_code_with_cbmc("""
    char global = 0;
    
    char func(char H, char m){
        global |= H & (1 << m);
        if (m < 8){
            func(H, m + 1);
        }
        return m;
    }
    
    void main()
    {
      char H = non_det_char();
      func(H, 0);
      char __out = global;
      END;
    }
    """, CBMCOptions(rec=0))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    dep, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 256

    assert math.log2(state.compute()) == 8


def test_recursion_without_effect():
    string = process_code_with_cbmc("""

    bool func(bool H){
        func(H);
        return 0;
    }

    void main()
    {
      func(non_det_bool());
      END;
    }
    """, CBMCOptions(rec=0))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    assert math.log2(state.compute()) == 0


def test_recursive_code_reduced_with_guard_and_abstract_rec():
    string = process_code_with_cbmc("""
bool fib(bool num){
  if (num)
  {
    return fib(num);
  }
  return num;
}

void main()
{
  bool __out = fib(non_det_bool());
  END;
}
""", CBMCOptions(rec=0, abstract_rec=0, verbose=True))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 1
    val = state.compute()
    assert val == 2  # was 256 before, but maybe this time it isn't ABI related (bool is an byte for ABI)?


def test_recursive_code_reduced_with_guard_and_abstract_rec2():
    string = process_code_with_cbmc("""
    bool fib(bool num){ return num ? !fib(num) : num; }
    void main()
    {
      bool __out = fib(non_det_bool());
      END;
    }
    """, CBMCOptions(rec=0, abstract_rec=0))
    assert State.from_string(string).compute() == 2  # the boolean negation


def test_recursive_code_reduced_with_guard_and_abstract_rec_small():
    string = process_code_with_cbmc("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool __out = fib(non_det_bool());
      END;
    }
    """, CBMCOptions(rec=0, abstract_rec=0))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 2
    val = state.compute()
    assert val == 2
    print(val)


def compute_with_abstract_rec(code: str, expected_deps: int) -> int:
    string = process_code_with_cbmc(code, CBMCOptions(rec=0, abstract_rec=0))
    state = State.from_string(string)
    assert len(state.cnf.deps) == expected_deps
    # ret, cnf, new_state = state.split()
    # available_variability = state._count_sat(cnf)
    # assert math.log2(available_variability) == 31
    val = state.compute()
    return math.log2(val)


def test_abstract_rec_with_double_rec():
    assert compute_with_abstract_rec("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool arg = non_det_bool();
      bool __out = fib(1) && fib(1);
      END;
    }
    """, expected_deps=2) == 0  # this is valid, as fib is a pure function (and its probably known in symex)


def test_abstract_rec_with_const_arg():
    assert compute_with_abstract_rec("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool __out = fib(1);
      END;
    }
    """, expected_deps=1) == 0


def test_fib_with_abstract_rec():
    """ Test case is base for test_abstract_rec_to_applicable() in test_recursion_graph """

    def check_graph(g: Graph):
        # the function fib should have a maximum variability of 9
        assert single(g.process_recursion_graph().max_variability) == 9
        # the return value of the function (and thereby __out) should be    (0) ? (1) : (2)    and therefore != (1)
        assert g.cnf.deps[0].ret != g.cnf.ind

    string = process_code_with_cbmc("""
char fib(char num){
  if (num > 0 && num < 9)  // (0)
  {
    return fib(num);  // num ~{max: 8}~{one constraint}~> ret    (1)
  }
  return 0;  //  (2)
}

void main()
{
  char __out = fib(non_det_char());
  END;
}

/*
Should be transformed into:

__out = (num > 1 && num < 9) ? (num ~{max:8}~> unknown) : 0 // this might produce 9 different numbers in the worst case
*/
""", CBMCOptions(rec=0, abstract_rec=0, process_graph=check_graph))
    state = State.from_string(string)
    assert len(state.cnf.deps) == 1
    dep = state.cnf.deps[0]
    assert len(dep.constraint) == 1
    ret, cnf, new_state = state.split()
    available_variability = state._count_sat(cnf)
    assert available_variability == 8
    assert state.compute() == 9


def test_basic_java():
    string = process_code_with_jbmc("""
    static int __out = 0;
    public static void main(String[] args) {
      int secret = non_det(); // get a random integer
      __out = secret;
      END;
    }
    """, )
    state = State.from_string(string)
    assert math.log2(state.compute()) == 32


def test_basic_java2():
    string = process_code_with_jbmc("""
    static int __out = 0;
    public static void main(String[] args) {
      int secret = non_det(); // get a random integer
       int val = secret | 1; // only uneven integers
      if (val > 32 || val < 0){
        val = 1;
      }
      __out = val;
      END;
    }
    """, )
    state = State.from_string(string)
    assert math.log2(state.compute()) == 4  # 16 uneven integers


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


MATestCases = {
    "electronic purse 1": {
        "code": """
        /* Toy program from paper of Backes et. al:  "Automatic */
        /* discovery and quantification of information leaks" */
        /* Should leak the whole secret */
        void main(){
            int h = non_det();
            int z = 0;
            while (h >= 1){
                h = h - 1;
                z = z + 1;
            }
            int __out = z;
            END;
        }
        """,
        "leakage": 32
    },
    "electronic purse 2": {
        "code": """
        /* Toy program from paper of Backes et. al:  "Automatic */
        /* discovery and quantification of information leaks" */
        /* Should leak the whole secret */
        void main(){
            int H = (char)non_det();
            int O = 0;
            while (H >= 5 && H < 20){ // problem: bit level lower operation is difficult
                H = H - 5;
                O = O + 1;
            }
            int __out = O;
            END;
        }
        """,
        "leakage": 32
    },
    "electronic purse 2 with unwinding 10": {
        "code": "electronic purse 2",
        "leakage": 32,
        "unwind": 10
    },
    "implicit flow": {
        "code": """
        /* Toy program from paper of Meng et. al: "Calculating bounds on information leakage using two-bit patterns" */
        /* https://github.com/qif/jpf-qif/blob/master/src/examples/plas/ImplicitFlow.java */
        /* Should leak log 7 = 2.8074 */
        void main(){
            int S = non_det();
            int O;
            if (S == 0) {
                O = 0;
            } else {
                if (S == 1) {
                   O = 1;
                } else {
                    if (S == 2) {
                        O = 2;
                    } else {
                        if (S == 3) {
                            O = 3;
                        } else {
                            if (S == 4) {
                                O = 4;
                            } else {
                                if (S == 5) {
                                    O = 5;
                                } else {
                                    if (S == 6) {
                                        O = 6;
                                    } else {
                                        O = 0;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            int __out = O;
            END;
        }
        """,
        "leakage": (2.8, 2.9)
    },
    # omitted the other test cases from https://github.com/parttimenerd/nildumu/blob/master/src/main/java/nildumu/eval/specimen/eval
    # that do not contain loops or recursion
    "binary search": {
        "code": """
        /* Z. Meng and G. Smith, Calculating Bounds on Information Leakage Using Two-bit Patterns, in Proceedings of the ACM SIGPLAN 6th Workshop on Programming Languages and Analysis for Security, 2011, p. 1:1--1:12. */
        /* Should leak 16 bits */
        void main(){
            unsigned int O = 0;
            unsigned int S = non_det();
            for (int i = 0; i < 16; i++) {
                unsigned int m = 1 << (31-i);
                if (O + m <= S) O += m;
            }
            unsigned int __out = O;
            END;
        }
        """,
        "leakage": 16,
        "unwind": 19
    },
    "dead fibonacci": {
        "code": """
        int fib(int num){
            int r = 1;
            if (r > 2){
                r = fib(num - 1) + fib(num - 2);
            }
            return r;
        }
        
        void main(){
            int h = non_det();
            int z = fib(h & 0b00000000000000000000000000011111);
            int __out = z;
            END;
        }
        """,
        "leakage": 0
    }
}


def _id_fn2(name_code_tuple: Tuple[str, dict]) -> str:
    return name_code_tuple[0]


class TestMATests:
    """ Tests used in my master thesis """

    @pytest.mark.parametrize(
        'name_code_tuple', sorted((f for f in MATestCases.items()), key=lambda x: x[0]),
        ids=_id_fn2
    )
    def test_all(self, name_code_tuple: Tuple[str, dict]):
        self.check(MATestCases, *name_code_tuple)

    @staticmethod
    def check(base: dict, name: str, d: dict):
        code = d["code"]
        if code in base:
            code = MATestCases[code]["code"]
        leakage = d["leakage"]
        unwind = d.get("unwind", 3)
        options = CBMCOptions(unwind=unwind)
        config = d.get("config", None)
        if isinstance(leakage, tuple):
            leakage_lower_bound, leakage_upper_bound = leakage
            assert leakage_lower_bound <= TestMATests.compute(code, config, options) <= leakage_upper_bound, name
        else:
            assert TestMATests.compute(code, config, options) == leakage

    @staticmethod
    def compute(code: str, config: Config = None, options: CBMCOptions = None) -> float:
        config = config or Config(xor_generator=RangeSplitXORGenerator())
        cnf = DCNF.load_string(process_code_with_cbmc(code, options))
        return math.log2(State(cnf, config).compute_loop(1))
