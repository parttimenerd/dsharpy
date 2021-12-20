""" Utilities not directly related to formulas or CNFs """
import functools
import logging
import os
import re
import subprocess
import tempfile
from collections import defaultdict
from typing import TYPE_CHECKING, Dict, Tuple

if TYPE_CHECKING:
    from _typeshed import ReadableBuffer
from dataclasses import dataclass, field
from io import IOBase

from pathlib import Path
from tempfile import NamedTemporaryFile
from types import TracebackType
from typing import TypeVar, List, Union, Any, Iterable, Optional, Type, Iterator

T = TypeVar("T")


def binary_path(program: str) -> Path:
    return Path(__file__).parent.parent.absolute() / "util" / program


def pprint(x: Any):
    import prettyprinter
    prettyprinter.install_extras(exclude=['ipython', 'ipython_repr_pretty'])
    prettyprinter.pprint(x)


@functools.lru_cache()
def modified_cbmc_path() -> Path:
    dsharpy_base = Path(__file__).parent.parent
    # if (dsharpy_base.parent / "cbmc").exists():  # we're clearly in my current debug setup
    #    return dsharpy_base.parent / "cbmc/build/bin/cbmc"
    return next(f for f in (dsharpy_base / "util" / "modified_cbmc" / "build").rglob("cbmc") if f.is_file()).absolute()


def has_modified_cbmc() -> bool:
    try:
        subprocess.run([str(modified_cbmc_path()), "-h"], check=True, capture_output=False, stdout=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


@functools.lru_cache()
def relationscutter_path() -> Path:
    dsharpy_base = Path(__file__).parent.parent
    # if (dsharpy_base.parent / "cbmc").exists():  # we're clearly in my current debug setup
    #    return dsharpy_base.parent / "cbmc/build/bin/cbmc"
    return next(f for f in (dsharpy_base / "util" / "relationscutter" / "build").rglob("relationscutter") if
                f.is_file()).absolute()


def has_relationscutter() -> bool:
    try:
        subprocess.run([str(relationscutter_path()), "-h"], check=True, capture_output=False, stdout=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


@dataclass
class CBMCOptions:
    unwind: int = 3
    rec: Optional[int] = None
    """ None: use unwind """
    abstract_rec: Optional[int] = None
    """ Use abstract with depth, None: don't use abstract recursion (and the expensive post processing) """
    preprocess: bool = True
    verbose: bool = False
    int_width: int = 32

    def __post_init__(self):
        assert self.unwind >= 3


@dataclass
class RelationsCutterOptions:
    input_prefixes: List[str] = field(default_factory=lambda: ["symex::nondet"])
    output_method: str = "main"
    output_ind_vars: List[str] = field(default_factory=lambda: ["__out"])
    verbose: bool = False


def process_code_with_cbmc(c_code: str, tmp_folder: Path, options: CBMCOptions = None,
                           file_ending: str = ".cpp") -> Path:
    """ Returns the temporary CNF file """
    with NamedTemporaryFile(suffix=file_ending, dir=tmp_folder, delete=False) as f:
        f.write(c_code.encode())
        f.flush()
        return process_path_with_cbmc(Path(f.name), tmp_folder, options)


def process_path_with_cbmc(c_file: Path, tmp_folder: Path, options: CBMCOptions = None) -> Path:
    """ Returns the temporary CNF file """
    if not c_file.exists():
        raise FileNotFoundError(f"File {c_file} not found")
    cnf_path = tmp_folder / (c_file.name + ".cnf")
    process_with_cbmc(c_file, cnf_path, options)
    return cnf_path


def preprocess_c_code(c_code: str) -> str:
    new_lines = ["#include <assert.h>",
                 "int non_det();",
                 "bool __non_det();",
                 "#define END assert(__non_det());",
                 """#define CONCAT(a, b) CONCAT_INNER(a, b)
#define CONCAT_INNER(a, b) a ## b
#define INPUT(type) CONCAT(non_det_, type)()"""]
    new_lines_to_add = []
    lines = c_code.split("\n")
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
    max_out_count: int = len(re.findall(r"LEAK\(", c_code))

    def replace_leak(match: re.Match):
        name = f"LEAK{'' if out_count[0] == 0 else out_count[0]}"
        out_count[0] += 1
        new_lines_to_add.append(f"#define {name}(value) typeof((value)) __out = (value); {'END;' if max_out_count == out_count[0] else ''}")
        return name + "("

    c_code = re.sub(r"LEAK\(", replace_leak, c_code)

    return "\n".join(new_lines_to_add + c_code.split("\n"))


def process_with_cbmc(c_file: Path, cnf_file: Path, options: CBMCOptions = None):
    options = options or CBMCOptions()
    if options.preprocess:
        with NamedTemporaryFile(suffix=c_file.suffix) as f:
            f.write(preprocess_c_code(c_file.read_text()).encode())
            f.flush()
            return run_cbmc(Path(f.name), cnf_file, options)
    else:
        return run_cbmc(c_file, cnf_file, options)


def run_cbmc(c_file: Union[Path, str], cnf_file: Path, options: CBMCOptions = None,
             cbmc_path: Path = modified_cbmc_path(),
             misc: List[str] = None, cwd: Path = None, verbose: bool = False):
    options = options or CBMCOptions()
    env = os.environ.copy()
    if options.rec is not None:
        env.update({"REC": str(options.rec)})
    if options.abstract_rec is not None:
        env.update({"REC_GRAPH_INLINING": str(options.abstract_rec), "REC": str(options.rec), "RELATIONS": "1"})
    env.update({"REC": str(options.rec), "RELATIONS": "1", "OMIT_SAT": "1"})
    cmd = [str(cbmc_path), str(c_file), f"--{options.int_width}", "--unwind", str(options.unwind), "--dimacs"] + (
                misc or [])
    if verbose:
        print(" ".join(cmd))
    res = subprocess.run(cmd,
                         stdout=subprocess.PIPE, bufsize=-1, stderr=subprocess.PIPE, env=env,
                         cwd=str(cwd) if cwd else os.getcwd())
    err = res.stderr.decode()
    cbmc_out = res.stdout.decode()
    if "Failed" in err or "Usage" in err or "ERROR" in err or "exception" in err \
            or "0" not in cbmc_out or " failed" in err or "segmentation fault" in err \
            or "segmentation fault" in cbmc_out or res.returncode < 0:
        raise BaseException("CBMC: " + err)

    if verbose or options.verbose:
        logging.info(err)
        logging.info(cbmc_out)
        if isinstance(c_file, Path) and verbose:
            print(c_file.read_text())
    cnf_file.write_text(cbmc_out)


def process_with_relationscutter(cnf_file: Path, options: RelationsCutterOptions = None,
                                 cutter_path: Path = relationscutter_path(),
                                 verbose: bool = False) -> int:
    options = options or RelationsCutterOptions()
    cmd = [str(cutter_path), str(cnf_file), "--method", options.output_method,
           "--input", ",".join(options.input_prefixes),
           "--output", ",".join(options.output_ind_vars)]
    if verbose:
        cmd.append("--verbose")
        print(" ".join(cmd))
    res = subprocess.run(cmd, stdout=subprocess.PIPE, bufsize=-1, stderr=subprocess.PIPE)
    err = res.stderr.decode()
    cutter_out = res.stdout.decode()

    if "Failed" in err or "Usage" in err or "ERROR" in err or "exception" in err \
            or "Leakage: " not in cutter_out or " failed" in err or "segmentation fault" in err \
            or "segmentation fault" in cutter_out or res.returncode < 0:  # or "[warning] " in cutter_out:
        print("====== returncode =======")
        print(res.returncode)
        raise BaseException("Relationscutter: " + err + "\n---\n" + cutter_out)

    if True or verbose or options.verbose:
        print(err)
        print(cutter_out)
    return int(cutter_out.split("Leakage: ")[1].split("\n")[0])


def process_with_options(code: Union[Path, str], cbmc_options: CBMCOptions = None,
                         cutter_options: RelationsCutterOptions = None) -> int:
    with tempfile.TemporaryDirectory() as tmpfolder:
        cnf_file = (process_path_with_cbmc if isinstance(code, Path) else process_code_with_cbmc)(code, Path(tmpfolder),
                                                                                                  cbmc_options)
        return process_with_relationscutter(cnf_file, cutter_options)


def process(code: Union[Path, str], real_unwind: int = 2, int_width: int = 32, verbose: bool = False) -> int:
    return process_with_options(code, CBMCOptions(unwind=real_unwind + 2, rec=real_unwind - 1, int_width=int_width,
                                                  verbose=verbose),
                                RelationsCutterOptions(verbose=verbose))
