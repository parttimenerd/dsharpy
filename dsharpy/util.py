""" Utilities not directly related to formulas or CNFs """
import copy
import random
import secrets
from pathlib import Path
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
    prettyprinter.install_extras()
    prettyprinter.pprint(x)
