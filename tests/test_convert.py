"""
Black box tests for the conversion and the modified CBMC
"""
import pytest

from dsharpy.formula import DCNF
from dsharpy.util import process_code_with_cbmc, CBMCOptions, DepGenerationPolicy
from tests.util import assert_deps_independent


def test_small_recursive_code():
    string = process_code_with_cbmc("""
    bool fib(bool num){
      return fib(num) & 1;
    }

    void main()
    {
      bool __out = fib(non_det_bool());
      END;
    }
    """, options=CBMCOptions(rec=0, abstract_rec=0, dep_gen_policy=DepGenerationPolicy.FULL_VARS))
    deps = DCNF.load_string(string).deps
    assert_deps_independent(deps)
    assert len(deps) == 1


@pytest.mark.parametrize(("opts", "dep_count"),
                         [(CBMCOptions(rec=0, abstract_rec=0, dep_gen_policy=DepGenerationPolicy.SINGLE_DEP), 1),
                          (CBMCOptions(rec=0, abstract_rec=None, dep_gen_policy=DepGenerationPolicy.SINGLE_DEP), 1),
                          (CBMCOptions(rec=0, abstract_rec=0, dep_gen_policy=DepGenerationPolicy.FULL_BITS), 8),
                          (CBMCOptions(rec=0, abstract_rec=0, dep_gen_policy=DepGenerationPolicy.FULL_VARS), 1)])
def test_recursive_code(opts, dep_count):
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
""", opts)
    deps = DCNF.load_string(string).deps
    assert_deps_independent(deps)
    assert len(deps) == dep_count


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
""")
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
""")
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
""", CBMCOptions(rec=0))
    dcnf = DCNF.load_string(string)
    assert len(dcnf.deps) == 1
    dep = dcnf.deps[0]
    assert len(dep.param) == 1, "bool parameter"
    assert len(dep.ret) == 8, "bool return, but this is C, so…"
    assert_deps_independent(dcnf.deps)
