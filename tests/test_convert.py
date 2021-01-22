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
    deps = DCNF.load_string(string).deps
    assert_deps_independent(deps)
    assert len(deps) == 1


def test_small_loop():
    string = process_code_with_cbmc("""
char non_det_char();

void main()
{
  char num = non_det_char();
  char res = 1;
  while (res < num) {
    res += 2;
  }
  char __out = res;
  assert(num != 0);
}
""", preprocess=True, unwind=3)
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
""", preprocess=True, unwind=3)
    dcnf = DCNF.load_string(string)
    assert len(dcnf.deps) == 1
    assert_deps_independent(dcnf.deps)


def test_recursive_code_reduced_with_guard():
    string = process_code_with_cbmc("""
bool fib(bool num){
  return num ? fib(num) : num;
}

void main()
{
  fib(non_det_bool()); 
  END;
}
""", rec=0)
    dcnf = DCNF.load_string(string)
    assert len(dcnf.deps) == 1
    dep = dcnf.deps[0]
    assert len(dep.param) == 1, "bool parameter"
    assert len(dep.ret) == 8, "bool return, but this is C, so…"
    assert_deps_independent(dcnf.deps)
