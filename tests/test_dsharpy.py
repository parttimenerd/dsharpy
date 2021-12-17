from typing import Tuple

import pytest

from dsharpy.util import process


def test_basic():
    assert process("""
void main()
{
  char __out = non_det();
  END;
}
""") == 8


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
  bool __out = fib(non_det_bool()); 
  // but the overall variability of the program should be 2
  // as it is unknown what fib(num) does
  END;
}
""", real_unwind=1) == 1


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
  char b = fib(non_det_char());
  char __out = b;
  END;
}
""", real_unwind=1) == 8


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
  char b = fib(non_det_char());
  char __out = b;
  END;
}
""", real_unwind=2) == 8


def test_multiple_outputs():
    assert process("""
void main()
{
  char __out = non_det();
  char __out2 = non_det();
  END;
}
""") == 16


def test_small_condition_loop():
        assert process("""
    void main()
    {
      char num = non_det_char();
      char res = 0;
      if (res != num) {
        res = 1;
      }
      char __out = res;
      END;
    }
    """, real_unwind=1, int_width=16) == 1


def test_smaller_loop():
    assert process("""
void main()
{
  char num = non_det_char();
  char res = 0;
  while (res != num) {
    res = 1;
  }
  char __out = res;
  END;
}
""", real_unwind=1, int_width=16) == 8

def test_small_loop():
    assert process("""
void main()
{
  char num = non_det_char();
  char res = 0;
  while (res < num) {
    res += 1;
  }
  char __out = res;
  END;
}
""", real_unwind=1) == 8


def test_small_loop_reduced():
    assert process("""
void main()
{
  char num = non_det_char();
  char res = 1;
  while (res != num) {
    res = res << 2;
  }
  char __out = res;
  END;
}
""", real_unwind=8) == 8


def test_small_loop2():
    assert process("""
void main()
{
  char num = non_det_char();
  char res = 1;
  while (res < num) {
    res *= 4;
    num *= 2;
  }
  char __out = res;
  END;
}
""") == 5


def test_small_loop3():
    assert process("""
void main()
{
  char num = non_det_char();
  char res = 1;
  while (res < num) {
    res *= 4;
    num++;
    num *= res == 2 ? 3 : 1;
  }
  char __out = res;
  END;
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
      char __out = i;
      END;
    }
    """) == 0


def test_fully_unwindable_loop():
    assert process("""
    void main()
    {
      char i = 0;
      while (i < 2) { i++; }
      END;
    }
    """) == 0


@pytest.mark.skip("takes 4 minutes")
def test_array_in_loop():
    assert process("""
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
    """) == 32


def test_array_in_loop_reduced():
    assert process("""
    void main()
    {
      char arr[10];
      char S = non_det();
      for (char i = 0; i < 10; i++){
        arr[i] = S & i;
      }
      char __out = arr[4];
      END;
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
      char H = non_det_char();
      func(H, 0);
      char __out = global;
      END;
    }
    """) == 8


@pytest.mark.parametrize("rec", [
    (0,),
    (5,)
])
def test_recursion_without_effect(rec: int):
    assert process("""
    bool func(){
        func();
        return 0;
    }

    void main()
    {
      func();
      END;
    }
    """) == 0


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
  bool __out = fib(non_det_bool());
  END;
}
""") == 2  # non_det_bool() returns a proper one bit bool (not the worst case for ABI, but ok nonetheless)


def test_recursive_code_reduced_with_guard_and_abstract_rec2():
    assert process("""
    bool fib(bool num){ return num ? !fib(num) : num; }
    void main()
    {
      bool __out = fib(non_det_bool());
      END;
    }
    """) == 2  # the boolean negation


def test_recursive_code_reduced_with_guard_and_abstract_rec_small():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool __out = fib(non_det_bool());
      END;
    }
    """, real_unwind=1) == 2



def test_abstract_rec_with_double_rec():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool __out = fib(1) && fib(1);
      END;
    }
    """) == 0  # this is valid, as fib is a pure function (and its probably known in symex)


def test_abstract_rec_with_const_arg():
    assert process("""
    bool fib(bool num){
      return fib(num);
    }

    void main()
    {
      bool __out = fib(1);
      END;
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
        char h = non_det_char();
        while (h != f(h)){
            h--;
        }
        char __out = f(h);
        END;
    }
    """) == 1


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
            int __out = O;
            END;
        }
        """,
        "leakage": (4, 32)
    },
    "electronic purse 2 with unwinding 10": {
        "code": "electronic purse 2",
        "leakage": 2,
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
        code: str = d["code"]
        if code in base:
            code: str = MATestCases[code]["code"]
        leakage = d["leakage"]
        unwind = d.get("unwind", 3)
        config = d.get("config", None)
        if isinstance(leakage, tuple):
            leakage_lower_bound, leakage_upper_bound = leakage
            assert leakage_lower_bound <= process(code, real_unwind=unwind) <= leakage_upper_bound, name
        else:
            assert process(code, real_unwind=unwind) == leakage