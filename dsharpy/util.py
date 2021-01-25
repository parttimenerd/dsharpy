""" Utilities not directly related to formulas or CNFs """
import copy
import functools
import math
import os
import random
import secrets
import subprocess
from io import IOBase

from io import StringIO
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TypeVar, List, Tuple, Set, Union, Sequence, Any, Iterable, Iterator, Dict


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
    if (dsharpy_base.parent / "cbmc").exists():  # were clearly in my current debug setup
        return dsharpy_base.parent / "cbmc/cmake-build-debug/bin/cbmc"
    return next(f for f in (dsharpy_base / "util" / "cbmc" / "build").rglob("cbmc") if f.is_file()).absolute()


def has_modified_cbmc() -> bool:
    try:
        subprocess.run([str(modified_cbmc_path()), "-h"], check=True, capture_output=False, stdout=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


def process_path_with_cbmc(c_file: Path, tmp_folder: Path, unwind: int = 3, rec: int = None, preprocess: bool = True) -> Path:
    """ Returns the temporary CNF file """
    if not c_file.exists():
        raise FileNotFoundError(f"File {c_file} not found")
    cnf_path = tmp_folder / (c_file.name + ".cnf")
    with c_file.open() as f:
        with cnf_path.open("w") as out:
            process_with_cbmc(Path(f.name), out, unwind, rec, preprocess)
    return cnf_path


def process_code_with_cbmc(c_code: str, unwind: int = 3, rec: int = None, file_ending: str = ".cpp", preprocess: bool = True) -> str:
    assert unwind >= 3
    out = StringIO()
    with NamedTemporaryFile(suffix=file_ending) as f:
        f.write(c_code.encode())
        f.flush()
        process_with_cbmc(Path(f.name), out, unwind, rec, preprocess)
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


def process_with_cbmc(c_file: Path, out: IOBase, unwind: int = 3, rec: int = None, preprocess: bool = False):
    if preprocess:
        with NamedTemporaryFile(suffix=c_file.suffix) as f:
            f.write(preprocess_c_code(c_file.read_text()).encode())
            f.flush()
            process_with_cbmc(Path(f.name), out, unwind, rec, preprocess=False)
        return
    my_env = os.environ.copy()
    if rec is not None:
        my_env.update({"REC": str(rec)})
    res = subprocess.run([modified_cbmc_path(), str(c_file), "--unwind", str(unwind), "--dimacs"],
                         stdout=subprocess.PIPE, bufsize=-1, stderr=subprocess.PIPE, env=my_env)
    err = res.stderr.decode()
    cbmc_out = res.stdout.decode()
    if "Failed" in err or "Usage" in err or "ERROR" in err or "exception" in err or "0" not in cbmc_out or " failed" in err:
        raise BaseException("CBMC: " + err)
    from dsharpy import convert

    #print(err)
    #print(cbmc_out)
    #print(c_file.read_text())
    convert.Graph.process(StringIO(cbmc_out), out, ind_var_prefix="__out")


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
