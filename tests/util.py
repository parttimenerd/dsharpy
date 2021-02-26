import logging
from pathlib import Path
from typing import Set, Union, FrozenSet

from dsharpy.formula import DCNF, Deps


logging.basicConfig(level=logging.INFO)


def load(name: str) -> DCNF:
    return DCNF.load(Path("cases") / name)


def check_independence(x: Union[FrozenSet[int], Set[int]], *others: Union[FrozenSet[int], Set[int]]) -> bool:
    xs = x.copy()
    for other in others:
        xs = xs.union(other)
    return len(xs) == len(x) + sum(len(other) for other in others)


def assert_deps_independent(deps: Deps):
    """
    Asserts that the dep parameters and returns are independent
    """
    for dep in deps:
        assert check_independence(dep.param, dep.ret), f"{dep}: param and ret have to be independent"
