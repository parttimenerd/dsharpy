"""
Black box tests for the conversion and the modified CBMC
"""

from dsharpy.formula import DCNF
from dsharpy.util import process_code_with_cbmc
from tests.util import assert_deps_independent


def test_recursive_code():
    string = process_code_with_cbmc("""
char fib(char num){
  if (num > 2)
  {
    return fib(num) + 1;
  }
  return num;
}

void main()
{
  char b = fib((char)non_det());
  char __out = b;
  assert(b + 1 != 0);
}
""", preprocess=True)
    assert_deps_independent(DCNF.load_string(string).deps)


def test_small_loop():
    string = process_code_with_cbmc("""
char non_det_char();

void main()
{
  char num = non_det_char();
  char res = 1;
  while (res < num) {
    res += 1;
  }
  char __out = res;
  assert(num != 0);
}
""", preprocess=True, unwind=2)
    dcnf = DCNF.load_string(string)
    assert len(dcnf.deps) == 1
    assert_deps_independent(dcnf.deps)


def test_small_loop_reduced():
    string = process_code_with_cbmc("""
char non_det_char();

void main()
{
  char num = non_det_char();
  char res = 1;
  while (res != num) {
    res *= 2;
  }
  char __out = res;
  char bla = num;
  assert(num != 0);
}
""", preprocess=True, unwind=2)
    dcnf = DCNF.load_string(string)
    assert len(dcnf.deps) == 1
    assert_deps_independent(dcnf.deps)
