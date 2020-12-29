""" Utilities not directly related to formulas or CNFs """
import copy
import functools
import os
import random
import secrets
import subprocess
import tempfile
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TypeVar, List, Tuple, Set, Union, Sequence, Any


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


def random_seed(seed: int):
    """ Set the random seed, useful for testing """
    random.seed(seed)


def random_exact_split(l: List[T]) -> Tuple[List[T], List[T]]:
    """ Split into two halves that have the same size (if possible) """
    shuffled = copy.copy(l)
    randomness.shuffle(shuffled)
    mid = int(len(shuffled) / 2)
    return shuffled[:mid], shuffled[mid:]


def random_choice(l: Union[Set[T], Sequence[T]]) -> T:
    if isinstance(l, set):
        return random_choice(tuple(l))
    return l[randomness.rand_int(len(l) - 1)]


def pprint(x: Any):
    import prettyprinter
    prettyprinter.install_extras(exclude=['django', 'ipython', 'ipython_repr_pretty'])
    prettyprinter.pprint(x)


@functools.lru_cache()
def modified_cbmc_path() -> Path:
    return next(f for f in (Path(__file__).parent.parent / "util" / "cbmc" / "build").rglob("cbmc") if f.is_file()).absolute()


def has_modified_cbmc() -> bool:
    try:
        subprocess.run([str(modified_cbmc_path()), "-h"], check=True, capture_output=False, stdout=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


def process_with_cbmc(c_file: Path, tmp_folder: Path, unwind: int = 3) -> Path:
    """ Returns the temporary CNF file """
    if not c_file.exists():
        raise FileNotFoundError(f"File {c_file} not found")
    out_path = tmp_folder / c_file.name
    cnf_path = tmp_folder / (c_file.name + ".cnf")
    res = subprocess.run([str(modified_cbmc_path()), str(c_file.absolute()), "--unwind", str(unwind), "--dimacs"],
                         stdout=out_path.open("w"), bufsize=-1, stderr=subprocess.PIPE)
    err = res.stderr.decode()
    if "Failed" in err or "Usage" in err:
        raise BaseException("CBMC: " + err)
    from dsharpy import convert
    convert.Graph.process(out_path, cnf_path)
    return cnf_path