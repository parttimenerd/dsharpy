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
