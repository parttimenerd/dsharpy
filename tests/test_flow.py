from typing import Tuple, List

from dsharpy.convert import method_regexp
from dsharpy.util import process_code_to_graph, CBMCOptions


def test_basic_api():
    graph = process_code_to_graph("""int func(int x, int y) {
    return x;
}

void main()
{
  char num = non_det_char();
  func(non_det_char(), non_det_char());
  assert(num != 0);
}""").create_summary_graph()
    assert graph.related(method_regexp("func", param="x"),
                         method_regexp("func", return_value=True))
    assert not graph.related(method_regexp("func", param="y"),
                             method_regexp("func", return_value=True))


def _check_basic_api(inner_code: str, related: List[Tuple[str, str]], unrelated: List[Tuple[str, str]]):
    graph = process_code_to_graph(f"""int func(int x, int y, int z) {{
    {inner_code}
    }}

    void main()
    {{
      char num = non_det_char();
      func(non_det_char(), non_det_char(), non_det_char());
      assert(num != 0);
    }}""").create_summary_graph()
    for from_, to_ in related:
        assert graph.related(method_regexp("func", param=from_),
                             method_regexp("func", param=to_))
    for from_, to_ in unrelated:
        assert not graph.related(method_regexp("func", param=from_),
                                 method_regexp("func", param=to_))


def test_basic_api2():
    _check_basic_api("return x + 1;", [("x", "return_value")], [("return_value", "x")])


def test_basic_api2():
    _check_basic_api("return x;", [("x", "return_value")], [("return_value", "x")])


def test_relation_direction():
    graph = process_code_to_graph("""
void main()
{
  char num = non_det_char();
  char yyy = num * 3;
  assert(num != 0);
}""").create_summary_graph()
    num_var = ".*num.*"
    y_var = ".*yyy.*"
    assert graph.related(num_var, y_var)
    assert not graph.related(y_var, num_var)
    assert graph.related(y_var, y_var)


def test_simple_endless_recursion():
    graph = process_code_to_graph("""
    char func(char arg, char arg2) {
        return !func(arg, arg);
    }
    
    void main()
    {
      char num1 = non_det_char();
      char num2 = non_det_char();
      char yyy = func(num1, num2);
      assert(non_det_char() != 0);
    }""").create_summary_graph()
    num1_var = ".*num1.*"
    num2_var = ".*num1.*"
    y_var = ".*yyy.*"
    assert graph.related(num1_var, y_var)
    assert not graph.related(y_var, num1_var)
    assert not graph.related(num2_var, y_var)
