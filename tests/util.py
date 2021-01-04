from pathlib import Path
from typing import Set, Union, FrozenSet

from dsharpy.formula import DCNF, Deps


def load(name: str) -> DCNF:
    return DCNF.load(Path("cases") / name)


def check_independence(x: Union[FrozenSet[int], Set[int]], y: Union[FrozenSet[int], Set[int]]) -> bool:
    return len(x.union(y)) == (len(x) + len(y))


def assert_deps_independent(deps: Deps):
    """
    Asserts that all deps consist of two independent sets
    """
    for x, y in deps.items():
        assert check_independence(x, y), f"{x} ~> {y}: both sets have to be independent"
