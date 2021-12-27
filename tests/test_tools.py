import logging
from typing import Tuple

import pytest

from dsharpy.preprocess import preprocess_c_code
from dsharpy.tools import MODEL_CHECKERS, LEAKAGE_COMPUTERS
import dsharpy.tools as tools

logging.basicConfig(level=logging.ERROR)


def process(code: str, mc: str = "modified_cbmc", lc: str = "relationscutter", unwind: int = 3, int_width: int = 32):
    mc = MODEL_CHECKERS[mc](unwind, bit_width=int_width)
    lc = LEAKAGE_COMPUTERS[lc]()
    return tools.process(mc, lc, code)


def test_process_invalid_code():
    with pytest.raises(BaseException):
        process("""
        void main()
        {
          int __out = non;_det();
          assert(__out);
        }
        """)


def test_basic():
    assert process("""
void main()
{
  LEAK(INPUT(char));
}
""") == 8


def test_basic_approxflow():
    assert process("""
void main()
{
  LEAK(INPUT(char));
}
""", lc="approxflow") == 8


def test_normal_cbmc_laundering_underapprox():
    assert process("""
void main()
{
  int h = INPUT(int);
  int o = 0;
  while (h != o) {
    o++;
  }
  LEAK(o);
}
""", lc="approxflow", mc="cbmc", unwind=8) == pytest.approx(3.2, 0.1)


def test_minimal_implicit_flow():
    assert process("""
    void main(){
        bool S = INPUT(bool);
        bool O = 0;
        if (S == 0) {
            O = 0;
        } else {
            O = 1;
        }
        LEAK(O);
    }
    """, int_width=16) == 1


def test_recursive_code_reduced_with_guard():
    assert process("""
bool fib(bool num){
  if (num)
  {
    return fib(num); // the variability of num should only be 1 
  }
  return num;
}

void main()
{
  LEAK(fib(INPUT(bool))); 
}
""", unwind=1) == 1


def test_recursive_code():
    assert process("""
char fib(char num){
  if (num > 2)
  {
    return fib(num + 1) + 1;
  }
  return num;
}

void main()
{
    LEAK(fib(INPUT(char)));
}
""", unwind=1) == 8


def test_recursive_code_real_fib():
    assert process("""
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
  LEAK(fib(INPUT(char)));
}
""", unwind=2) == 8


def test_multiple_outputs():
    assert process("""
void main()
{
  LEAK(INPUT(char));
  LEAK(INPUT(char))
}
""") == 16


def test_small_condition_loop():
    assert process("""
    void main()
    {
      char num = INPUT(char);
      char res = 0;
      if (res != num) {
        res = 1;
      }
      LEAK(res);
    }
    """, unwind=1, int_width=16) == 1


def test_smaller_loop():
    assert process("""
void main()
{
  char num = INPUT(char);
  char res = 0;
  while (res != num) {
    res = 1;
  }
  LEAK(res);
}
""", unwind=1, int_width=16) == 8


def test_small_loop():
    assert process("""
void main()
{
  char num = INPUT(char);
  char res = 0;
  while (res < num) {
    res += 1;
  }
  LEAK(res);
}
""", unwind=1) == 8


def test_small_loop_reduced():
    assert process("""
void main()
{
  char num = INPUT(char);
  char res = 1;
  while (res != num) {
    res = res << 2;
  }
  LEAK(res);
}
""", unwind=8) == 8


def test_small_loop2():
    assert process("""
void main()
{
  char num = INPUT(char);
  char res = 1;
  while (res < num) {
    res *= 4;
    num *= 2;
  }
  LEAK(res);
}
""") == 8


def test_small_loop3():
    assert process("""
void main()
{
  char num = INPUT(char);
  char res = 1;
  while (res < num) {
    res *= 4;
    num++;
    num *= res == 2 ? 3 : 1;
  }
  LEAK(res);
}
""") == 8


def test_a_loop_without_private_input():
    assert process("""
    void main()
    {
      char i = 0;
      while (i < 1){
        i = i << 1;
      }
      LEAK(i);
    }
    """) == 0


@pytest.mark.parametrize("unwind,leakage", [(2, 8), (1, 8), (3, 0)])
def test_fully_unwindable_loop(unwind: int, leakage: int):
    assert process("""
    void main()
    {
      char i = 0;
      while (i < 2) { i++; }
      LEAK(i);
    }
    """, unwind=3) == 0


@pytest.mark.skip("takes 4 minutes")
def test_array_in_loop():
    assert process("""
    void main()
    {
      int arr[10];
      int S = INPUT(int);
      for (int i = 0; i < 10; i++){
        arr[i] = S & i;
      }
      LEAK(arr[4]);
    }
    """) == 32


def test_array_in_loop_reduced():
    assert process("""
    void main()
    {
      char arr[10];
      char S = INPUT(char);
      for (char i = 0; i < 10; i++){
        arr[i] = S & i;
      }
      LEAK(arr[4]);
    }
    """) == 8


def test_global_variables_with_recursion():
    assert process("""
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
      char H = INPUT(char);
      func(H, 0);
      LEAK(global);
    }
    """) == 8


def test_recursive_code_reduced_with_guard_and_abstract_rec():
    assert process("""
bool fib(bool num){
  if (num)
  {
    return fib(num);
  }
  return num;
}

void main()
{
  LEAK(fib(INPUT(bool)));
}
""") == 1


def test_recursive_code_reduced_with_guard_and_abstract_rec2():
    assert process("""
    bool fib(bool num){ return num ? !fib(num) : num; }
    void main()
    {
      LEAK(fib(INPUT(bool)));
    }
    """) == 1  # the boolean negation


def test_recursive_code_reduced_with_guard_and_abstract_rec_small():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      LEAK(fib(INPUT(bool)));
    }
    """, unwind=1) == 1


def test_abstract_rec_with_double_rec():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      LEAK(fib(1) && fib(1));
    }
    """) == 0


def test_abstract_rec_with_const_arg():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      LEAK(fib(1));
    }
    """) == 0


def test_loops_and_recursion_mixed():
    assert process("""
    char r(char c){
        char a = 0;
        while (a < c){
            a++;
            c--;
        }
        return a;
    }   
    
    char f(char a){
        if (a < 0){
            return f(a + 1);
        }
        return r(a);
    }
    
    void main(){
        char h = INPUT(char);
        while (h != f(h)){
            h--;
        }
        LEAK(f(h));
    }
    """) == 8


MATestCases = {
    "electronic purse 1": {
        "code": """
        /* Toy program from paper of Backes et. al:  "Automatic */
        /* discovery and quantification of information leaks" */
        /* Should leak the whole secret */
        void main(){
            int h = INPUT(int);
            int z = 0;
            while (h >= 1){
                h = h - 1;
                z = z + 1;
            }
            LEAK(z);
        }
        """,
        "leakage": (31, 32)
    },
    "electronic purse 2": {
        "code": """
        /* Toy program from paper of Backes et. al:  "Automatic */
        /* discovery and quantification of information leaks" */
        void main(){
            int H = (char)non_det();
            int O = 0;
            while (H >= 5 && H < 20){ // problem: bit level lower operation is difficult
                H = H - 5;
                O = O + 1;
            }
            LEAK(O);
        }
        """,
        "leakage": (4, 32)
    },
    "electronic purse 2 with unwinding 10": {
        "code": "electronic purse 2",
        "leakage": 8,
        "unwind": 10
    },
    "implicit flow": {
        "code": """
        /* Toy program from paper of Meng et. al: "Calculating bounds on information leakage using two-bit patterns" */
        /* https://github.com/qif/jpf-qif/blob/master/src/examples/plas/ImplicitFlow.java */
        /* Should leak log 7 = 2.8074 */
        void main(){
            int S = INPUT(int);
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
            LEAK(O);
        }
        """,
        "leakage": 3
    },
    # omitted the other test cases from https://github.com/parttimenerd/nildumu/blob/master/src/main/java/nildumu/eval/specimen/eval
    # that do not contain loops or recursion
    "binary search": {
        "code": """
        /* Z. Meng and G. Smith, Calculating Bounds on Information Leakage Using Two-bit Patterns, in Proceedings of the ACM SIGPLAN 6th Workshop on Programming Languages and Analysis for Security, 2011, p. 1:1--1:12. */
        /* Should leak 16 bits */
        void main(){
            unsigned int O = 0;
            unsigned int S = INPUT(unsigned int);
            for (int i = 0; i < 16; i++) {
                unsigned int m = 1 << (31-i);
                if (O + m <= S) O += m;
            }
            LEAK(O);
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
            int h = INPUT(int);
            int z = fib(h & 0b00000000000000000000000000011111);
            LEAK(z);
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
        code: str = d["code"]
        if code in base:
            code: str = MATestCases[code]["code"]
        leakage = d["leakage"]
        unwind = d.get("unwind", 3)
        config = d.get("config", None)
        if isinstance(leakage, tuple):
            leakage_lower_bound, leakage_upper_bound = leakage
            assert leakage_lower_bound <= process(code, unwind=unwind) <= leakage_upper_bound, name
        else:
            assert process(code, unwind=unwind) == leakage


def test_approxflow_binsearch16():
    assert process("""
    #define BITS 16

int main() {
    unsigned int I = INPUT(unsigned int);

    unsigned int O = 0;

    unsigned int m;
    int i;

    for (i = 0; i < BITS; i++) {
      m = 1;
      if (O + m <= I) O += m;
    }
    LEAK(O);
}
""", lc="approxflow", mc="cbmc", unwind=8) == 8


def test_approxflow_electronic_purse():
    program = """
    #include <assert.h>
int nondet();
int nondet2();

int main() {
  int H = nondet();
  int O = 0;
  while (H >= 5 && H < 20){
      H = H - 5;
      O = O + 1;
  }
  int __out = O;
  assert(nondet2());
}
    """
    print(preprocess_c_code(program))
    assert process(program, lc="approxflow", mc="cbmc", unwind=8) == 2
