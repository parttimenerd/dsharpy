""" Utilities not directly related to formulas or CNFs """
import copy
import functools
import logging
import math
import os
import random
import secrets
import subprocess
import tempfile
from collections import deque
from dataclasses import dataclass, field
from enum import Enum
from io import IOBase

from io import StringIO
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TypeVar, List, Tuple, Set, Union, Sequence, Any, Iterable, Mapping, Callable, Optional, Deque, \
    Literal


def binary_path(program: str) -> Path:
    return Path(__file__).parent.parent.absolute() / "util" / program


T = TypeVar("T")


class SourceOfRandomness:

    def rand_int(self, max: int) -> int:
        """ Returns an integer >= 0 and <= max """
        raise NotImplementedError()

    def shuffle(self, x: List[T]):
        """
        source: random.shuffle

        Shuffle list x in place, and return None.

        Optional argument random is a 0-argument function returning a
        random float in [0.0, 1.0); if it is the default None, the
        standard random.random will be used.

        """
        _int = int
        for i in reversed(range(1, len(x))):
            # pick an element in x[:i+1] with which to exchange x[i]
            j = self.rand_int(i)
            x[i], x[j] = x[j], x[i]


class RandomRandom(SourceOfRandomness):

    def rand_int(self, max: int) -> int:
        return random.randint(0, max)


class SecretRandom(SourceOfRandomness):

    def rand_int(self, max: int) -> int:
        return secrets.randbelow(max + 1)


randomness = RandomRandom()


def random_int(min: int, max: int):
    """ Returns a random number >= min and <= max """
    return randomness.rand_int(max - min) + min


def random_bool() -> bool:
    return random_int(0, 1) == 0


def random_seed(seed: int):
    """ Set the random seed, useful for testing """
    random.seed(seed)


def random_exact_split(l: List[T]) -> Tuple[List[T], List[T]]:
    """ Split into two halves that have the same size (if possible) """
    shuffled = copy.copy(l)
    randomness.shuffle(shuffled)
    mid = int(len(shuffled) / 2)
    return shuffled[:mid], shuffled[mid:]


def random_split(l: List[T], n: int, min_size: int = 0) -> List[List[T]]:
    """ Split n parts with at least min_size elements each """
    assert min_size * n <= len(l)
    if n == 0:
        return []
    shuffled = random_shuffle(l)
    ret = [[] for i in range(n)]
    if min_size > 0:
        for i, part_list in enumerate(ret):
            part_list.extend(shuffled[i * min_size:(i + 1) * min_size])
    for e in shuffled[min_size * n:]:
        ret[random_int(0, len(ret) - 1)].append(e)
    return ret


def random_choice(l: Union[Set[T], Sequence[T]]) -> T:
    if isinstance(l, set):
        return random_choice(tuple(l))
    return l[randomness.rand_int(len(l) - 1)]


def random_shuffle(l: List[T]) -> List[T]:
    shuffled = copy.copy(l)
    randomness.shuffle(shuffled)
    return shuffled


def pprint(x: Any):
    import prettyprinter
    prettyprinter.install_extras(exclude=['django', 'ipython', 'ipython_repr_pretty'])
    prettyprinter.pprint(x)


@functools.lru_cache()
def modified_cbmc_path() -> Path:
    dsharpy_base = Path(__file__).parent.parent
    if (dsharpy_base.parent / "cbmc").exists():  # we're clearly in my current debug setup
        return dsharpy_base.parent / "cbmc/cmake-build-debug/bin/cbmc"
    return next(f for f in (dsharpy_base / "util" / "cbmc" / "build").rglob("cbmc") if f.is_file()).absolute()


def jbmc_models_path() -> Path:
    return (Path(__file__).parent.parent / "util" / "cbmc" / "jbmc" / "lib" / "java-models-library" / "target").absolute()


def jbmc_models_classpath() -> str:
    return f"{jbmc_models_path()}/core-models.jar:{jbmc_models_path()}/cprover-api.jar"


def has_modified_cbmc() -> bool:
    try:
        subprocess.run([str(modified_cbmc_path()), "-h"], check=True, capture_output=False, stdout=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


def mis_path() -> Path:
    p = binary_path("mis")
    assert (p / "muser2-dir/src/tools/muser2/muser2").exists(), "muser has to be compiled, use ./update.sh"
    return p / "mis.py"


class DepGenerationPolicy(Enum):
    """
    Policy for generating deps, important for multiple returns/outputs, else all are equivalent to SINGLE_DEP
    """

    SINGLE_DEP = "single_dep"
    """
    A single dep for all connections of loop iteration or function, ignores
    all return variables that are not related to a param

    Advantages:
    - simple
    """

    FULL_VARS = "full"
    """
    A dep per (equivalence class of parameters x related returns) (same for loops)

    Advantages:
    - over approximates to the utmost extent
    """

    MULTIPLE_DEP_VARS = "multiple_dep"
    """
    A dep per (equivalence class of parameters, related returns) (same for loops)
    """

    FULL_BITS = "full_bits"
    MULTIPLE_DEP_BITS = "multiple_dep_bits"

    def on_var_basis(self) -> bool:
        """ Based on whole variables (not just single SAT variables)"""
        return self == self.SINGLE_DEP or self == self.FULL_VARS or self == self.MULTIPLE_DEP_VARS


@dataclass
class CBMCOptions:
    unwind: int = 3
    rec: Optional[int] = None
    """ None: use unwind """
    abstract_rec: Optional[int] = 0
    """ Use abstract with depth, None: don't use abstract recursion (and the expensive post processing) """
    dep_gen_policy: DepGenerationPolicy = DepGenerationPolicy.FULL_VARS
    preprocess: bool = True
    verbose: bool = False
    compute_max_vars: bool = True
    process_graph: Callable[["convert.Graph"], None] = field(default_factory=lambda: (lambda g: None))
    counter_config: Optional["Config"] = None
    """ Only used for configuring the max var counter """

    def __post_init__(self):
        assert self.unwind >= 3


def process_path_with_cbmc(c_file: Path, tmp_folder: Path, options: CBMCOptions = None) -> Path:
    """ Returns the temporary CNF file """
    if not c_file.exists():
        raise FileNotFoundError(f"File {c_file} not found")
    cnf_path = tmp_folder / (c_file.name + ".cnf")
    with c_file.open() as f:
        with cnf_path.open("w") as out:
            process_with_cbmc(Path(f.name), out, options)
    return cnf_path


def process_code_with_cbmc(c_code: str, options: CBMCOptions = None,
                           file_ending: str = ".cpp") -> str:
    out = StringIO()
    with NamedTemporaryFile(suffix=file_ending) as f:
        f.write(c_code.encode())
        f.flush()
        process_with_cbmc(Path(f.name), out, options)
    return out.getvalue()


def preprocess_c_code(c_code: str) -> str:
    """ Add "int non_det();" and "#include <assert.h>" if not already present """
    new_lines = ["#include <assert.h>", "int non_det();", "char non_det_char();",
                 "char non_det_bool();",
                 "bool __non_det();", "#define END assert(__non_det());"]
    new_lines_to_add = []
    lines = c_code.split("\n")
    for new_line in new_lines:
        if new_line not in c_code:
            new_lines_to_add.append(new_line)
    return "\n".join(new_lines_to_add + lines)


def process_with_cbmc(c_file: Path, out: IOBase, options: CBMCOptions = None):
    options = options or CBMCOptions()
    if options.preprocess:
        with NamedTemporaryFile(suffix=c_file.suffix) as f:
            f.write(preprocess_c_code(c_file.read_text()).encode())
            f.flush()
            run_cbmc(Path(f.name), out, options)
    else:
        run_cbmc(c_file, out, options)


def run_cbmc(c_file: Union[Path, str], out: IOBase, options: CBMCOptions = None, cbmc_path: Path = modified_cbmc_path(),
             misc: List[str] = None, cwd: Path = None, verbose: bool = False, use_latest_ind_var: bool = True):
    options = options or CBMCOptions()
    env = os.environ.copy()
    if options.rec is not None:
        env.update({"REC": str(options.rec)})
    if options.abstract_rec is not None:
        env.update({"REC_GRAPH_INLINING": str(options.abstract_rec)})
    cmd = [str(cbmc_path), str(c_file), "--unwind", str(options.unwind), "--dimacs"] + (misc or [])
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
    from dsharpy import convert

    if verbose or options.verbose:
        logging.info(err)
        logging.info(cbmc_out)
        if isinstance(c_file, Path) and verbose:
            print(c_file.read_text())
    graph = convert.Graph.parse_graph(cbmc_out.split("\n"), options.dep_gen_policy,
                                      "__out", use_latest_ind_var=True, compute_max_vars=options.compute_max_vars,
                                      counter_conf=options.counter_config)
    options.process_graph(graph)
    graph.cnf.to_fp(out)


class JavaSourceType(Enum):

    JAVA = ".java"


def preprocess_java(code: str):
    return f"""
    import org.cprover.CProver;
    public class __base_class {{
        
        static int non_det(){{ return CProver.nondetInt(); }}
        
        static char non_det_char(){{ return CProver.nondetChar(); }}
        
        static boolean non_det_bool(){{ return CProver.nondetBoolean(); }}
        
        {code.replace('END', 'assert(CProver.nondetBoolean())')}
    
    }}
    """


def build_java(code: str) -> Path:
    tmp_dir = Path(tempfile.mkdtemp())
    tmp_dir2 = Path(tempfile.mkdtemp())
    java_file = tmp_dir2 / "__base_class.java"
    java_file.write_text(code)
    cmd = f"cd {tmp_dir.absolute()}; javac {java_file.absolute()} -cp {jbmc_models_classpath()} -d ."
    subprocess.check_call(cmd, shell=True)
    return tmp_dir


def process_code_with_jbmc(code: str, code_type: JavaSourceType = JavaSourceType.JAVA, options: CBMCOptions = None) -> str:
    options = options or CBMCOptions()
    assert options.preprocess
    out = StringIO()
    classpath = build_java(preprocess_java(code)).absolute()
    run_cbmc("__base_class", out, options, cbmc_path=modified_cbmc_path().parent / "jbmc",
             misc=["--classpath", f"{jbmc_models_classpath()}:{classpath}"], cwd=classpath)
    return out.getvalue()


def detect_file_suffix(content: str) -> Optional[Literal[".java", ".cpp", ".cnf"]]:
    """
    Detect a files suffix based on its content.

    Java files contain a Java style main method,
    CNF files are parseable by DCNF and
    C/C++ files contain all of "{}();" and a main method with void or int return value.
    """
    if "main(String[] args)" in content:
        return ".java"
    try:
        from dsharpy.formula import DCNF
        DCNF.load_string(content)
        return ".cnf"
    except:
        pass
    if all(x in content for x in "{}();") and \
            ("int main(" in content or "void main(" in content):
        return ".cpp"
    return None


def empty(iterable: Iterable) -> bool:
    """ Attention: works not for Iterators """
    return not any(True for i in iterable)


def to_bit_ceil(val: float) -> int:
    return math.ceil(math.log2(val))


def bit_count(i: int) -> int:
    """
    Count the set bits in i, for non-negative integers only
    """
    assert i >= 0
    count = 0
    while i > 0:
        count += i & 0b1
        i //= 2
    return count


@functools.lru_cache()
def ints_with_even_bit_count(max_int: int) -> List[int]:
    """ Ints with even bit count, up to max_int (inclusive) """
    return [i for i in range(max_int + 1) if bit_count(i) % 2 == 0]


K = TypeVar("K")
V = TypeVar("V")


def single(d: Mapping[K, V]) -> V:
    return next(iter(d.values()))


def bfs(start: Iterable[T], visit: Callable[[T], Optional[Iterable[T]]]):
    visited: Set[T] = set()
    deq: Deque[T] = deque()
    deq.extend(start)
    while len(deq) > 0:
        top = deq.pop()
        if top in visited:
            continue
        visited.add(top)
        top_v = visit(top)
        if top_v:
            deq.extendleft(top_v)
