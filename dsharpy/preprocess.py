import re
from collections import defaultdict
from typing import Dict, List


def preprocess_c_code(c_code: str, out_var_prefix: str = "__out") -> str:
    """
    Preprocesses c code to make it easier to write example programs for information flow.
    It does add
    - `#include <assert.h>` to use asserts
    - `INPUT(type)` to get a random (and therefore input) value of the specified type
    - `OBSERVE(expr)` that assigns the passed expression to a new output variable, the last leak also adds an assert
      to force the model checker to produce a SAT formula

    This code uses regular expressions and C macros…
    :param c_code: code to preprocess
    :param out_var_prefix: prefix of the output variables
    :return: preprocessed code
    """
    new_lines = ["#include <assert.h>",
                 "int non_det();",
                 "bool __non_det();",
                 "#define END assert(__non_det());",
                 """#define CONCAT(a, b) CONCAT_INNER(a, b)
#define CONCAT_INNER(a, b) a ## b
#define INPUT(type) CONCAT(non_det_, type)()"""]
    new_lines_to_add = []
    for new_line in new_lines:
        if new_line not in c_code:
            new_lines_to_add.append(new_line)
    type_func_count: Dict[str, int] = defaultdict(lambda: 0)

    def replace_input(match: re.Match):
        type = re.findall(r"INPUT\(([^)]+)\)", match.group())[0]
        count = type_func_count[type]
        name = f"non_det_{re.sub(type, '[^a-zA-Z0-9]', '___')}" + (f"___{count}" if count > 0 else "")
        type_func_count[type] = count + 1
        new_lines_to_add.append(f"{type} {name}();")
        return f"({name}(){'& 1' if type == 'bool' else ''})"

    c_code = re.sub(r"INPUT\(([^)]+)\)", replace_input, c_code)

    out_count: List[int] = [0]
    max_out_count: int = len(re.findall(r"OBSERVE\(", c_code))

    def replace_leak(match: re.Match):
        name = f"OBSERVE{'' if out_count[0] == 0 else out_count[0]}"
        out_count[0] += 1
        new_lines_to_add.append(f"#define {name}(value) typeof((value)) {out_var_prefix}{out_count[0] if out_count[0] else ''} = (value); {'END;' if max_out_count == out_count[0] else ''}")
        return name + "("

    c_code = re.sub(r"OBSERVE\(", replace_leak, c_code)

    return "\n".join(new_lines_to_add + c_code.split("\n"))
