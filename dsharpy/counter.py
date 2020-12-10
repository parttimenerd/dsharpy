import math
import os
from dataclasses import dataclass, field
from pathlib import Path
from statistics import median
from typing import Tuple, Set, List, Dict, Optional, Union

import click as click
from prettyprinter import register_pretty, pretty_call

from dsharpy.formula import Independents, blast_xor, count_sat, DCNF, sum_is_one2, sum_is_one4, sat
from dsharpy.util import random_exact_split, random_choice, pprint, random_seed

Dep = Tuple[int, int]

DepSet = Set[Dep]
""" Set of avaible dependencies  a ~> b"""


@dataclass(frozen=True)
class UninterpretedFunction:
    """ A relation between two variables with possible interpretations """

    dep: Dep
    interpretations: List[int] = field(default_factory=lambda: [1, 2, 3, 4])
    """ List of interpretations (δ_dep)"""

    def __post_init__(self):
        assert 1 <= len(self.interpretations) <= 4

    def __len__(self):
        return len(self.interpretations)

    def is_fixed(self) -> bool:
        return len(self) == 1

    def split(self) -> Tuple['UninterpretedFunction', 'UninterpretedFunction']:
        """ Split into two halfes randomly, both halves should have the same size """
        assert not self.is_fixed()
        return tuple(UninterpretedFunction(self.dep, l) for l in random_exact_split(self.interpretations))

    def to_cnf(self, last_id: int) -> List[List[int]]:
        """ ⋀_i b_i → to_cnf(i)   ∧   xor b_i """
        assert last_id >= max(self.dep)
        if self.is_fixed():
            return self.to_single_cnf(self.dep, self.interpretations[0])
        bs = [last_id + 1 + i for i in range(len(self.interpretations))]
        last_var = last_id + len(bs)
        impl_part = [[-bs[i]] + clause for i, inter in enumerate(self.interpretations)
                for clause in self.to_single_cnf(self.dep, inter)]
        if len(bs) == 2:
            return impl_part + sum_is_one2(*bs)
        if len(bs) == 4:
            return impl_part + sum_is_one4(*bs, new_var1=last_var + 1, new_var2=last_var + 2)
        assert False

    def __str__(self) -> str:
        return f"UI{self.dep}{self.interpretations}"

    def __repr__(self) -> str:
        return str(self)

    @staticmethod
    def to_single_cnf(dep: Dep, interpretation: int) -> List[List[int]]:
        assert 0 < interpretation <= 4
        a, b = dep
        if interpretation == 1:
            return [[b]]
        if interpretation == 2:
            return [[-a, b], [a, -b]]  # a ←→ b
        if interpretation == 3:
            return [[-a, -b], [a, b]]  # a ←→ -b
        if interpretation == 4:
            return [[-b]]
        assert False


@register_pretty(UninterpretedFunction)
def pretty_ui(value: UninterpretedFunction, ctx):
    return pretty_call(ctx, "", str(value))


@dataclass
class Config:
    parallelism: int = 2
    """ 
    a power of two, the log2 corresponds to the number of dimensions that are split and compared at once
    (independent dimensions can be seen as one)
    """
    amc_epsilon: float = 0.8
    amc_delta: float = 0.2
    amc_forcesolextension: bool = False
    log_iterations: bool = False
    epsilon: float = 0.2
    delta: float = 0.8

    def __post_init__(self):
        rel = math.log2(self.parallelism)
        assert int(rel) == math.ceil(rel) and rel >= 1


@dataclass(frozen=True)
class State:
    config: Config
    cnf: DCNF
    """ Base formula """
    independents: Independents
    deps: DepSet
    functions: Dict[Dep, UninterpretedFunction]
    volatile_deps: List[Dep]
    """ Deps with |functions[d]| > 1 """

    def split(self, pivots: List[Dep]) -> Tuple['State', 'State']:
        """
        Split into two states at the passed deps.

        Attention: using more than one pivot increases the performance but might hamper the soundness if
        the pivot deps are not entirely independent

        \forall s \in pivots: |A_1[s]| + |A_2[s]| = |A[s]| / |pivots|
        """
        new_functions: Tuple[List[UninterpretedFunction],
                             List[UninterpretedFunction]] = ([], [])
        for pivot in pivots:
            l, r = self.functions[pivot].split()
            new_functions[0].append(l)
            new_functions[1].append(r)
        ret: List[State] = []
        for func_list in new_functions:
            copy = self.functions.copy()
            for func in func_list:
                copy[func.dep] = func
            ret.append(State(self.config, self.cnf, self.independents,
                             self.deps, copy, self.volatile_deps))
        return tuple(ret)

    def choose_and_split(self, depth: int = None) -> List['State']:
        """ Split the current state into 2^depth states """
        depth = math.log2(self.config.parallelism) if depth is None else depth
        if depth == 0 or not self.can_still_choose():
            return [self]
        pivots, state = self.choose_and_remove()
        left, right = state.split(pivots)
        return left.choose_and_split(depth - 1) + right.choose_and_split(depth - 1)

    def choose_and_remove(self) -> [List[int], 'State']:
        """
        Chooses a list of pivot elements.

        Chooses a random independents set and for all the elements a random depset if there are indies left,
        else chooses a random depset
        """
        if len(self.independents) > 0:
            indie_set = random_choice(self.independents)
            to_remove = [dep for dep in indie_set if len(self.functions[dep]) == 2]
            if to_remove:
                copy = self.volatile_deps.copy()
                copy_indie = indie_set.copy()
                copy_indies = self.independents.copy()
                for dep in to_remove:
                    copy.remove(dep)
                    copy_indie.remove(dep)
                if not copy_indie:
                    copy_indies.remove(indie_set)
                copy_indies.append(copy_indie)
                return indie_set, State(self.config, self.cnf, copy_indies, self.deps, self.functions, copy)
            return indie_set, State(self.config, self.cnf, self.independents, self.deps, self.functions, self.volatile_deps)
        pivot = random_choice(self.volatile_deps)
        copy = self.volatile_deps
        if len(self.functions[pivot]) == 2:
            copy = copy.copy()
            copy.remove(pivot)
        return [pivot], State(self.config, self.cnf, self.independents, self.deps, self.functions, copy)

    def can_still_choose(self) -> bool:
        return len(self.volatile_deps) > 0

    def is_surely_unsat(self) -> bool:
        """
        Check if the current configuration is surely unsat or if has the possibility to be sat.

        Might use only a subset the overall formula.

        Only an optimization, implement if neccessary
        """
        return False

    def to_cnf(self) -> DCNF:
        cnf = self.cnf.shallow_copy()
        for func in self.functions.values():
            for clause in func.to_cnf(cnf.nv):
                cnf.append(clause)
        return cnf

    @classmethod
    def from_dcnf(cls, dcnf: DCNF, config: Config = None) -> 'State':
        deps = dcnf.get_dep_relations()
        return State(config or Config(), dcnf, dcnf.independents, deps,
                     {dep: UninterpretedFunction(dep) for dep in deps},
                     deps)

    @classmethod
    def from_string(cls, string: str, config: Config = None) -> 'State':
        return cls.from_dcnf(DCNF.load_string(string), config)

    def _count_sat(self, cnf: Union[List[DCNF], DCNF]) -> Union[List[Optional[float]], Optional[float]]:
        return count_sat(cnf, epsilon=self.config.amc_epsilon,
                         delta=self.config.amc_delta,
                         forcesolextension=self.config.amc_forcesolextension)

    def compute(self) -> float:
        """ Approximately compute the model count with respect to the dependencies """
        if not self.cnf.clauses:
            return 0
        cur = self
        max_count = -1.0
        if not cur.can_still_choose():
            return self._count_sat(self.to_cnf())
        while cur.can_still_choose():
            states = cur.choose_and_split()
            print(len(states))
            ret = self._count_sat([state.to_cnf() for state in states])
            if self.config.log_iterations:
                pprint(states)
            ret2: List[float] = [r if r else -1 for r in ret]
            max_count = max(ret2)
            if self.config.log_iterations:
                print("round " + str(max_count) + " " + str(ret))
            if max_count == -1:
                # TODO: if max_count = -1: return max and log warning
                print("warning")
                return max_count
            cur = states[ret2.index(max_count)]
        return max_count

    def compute_loop(self, runs: int = 3) -> float:
        if not sat(self.cnf):
            return -1
        counts: List[float] = []
        for run in range(runs):
            count = self.compute()
            counts.append(count)
            if self.config.log_iterations:
                print(f"-- run {run:2d}: {count:3f}     median = {median(counts):3f}  max = {max(counts):3f}")
        return max(counts)



@click.command(name="dsharpy", help="An approximate model counter with dependencies based on ApproxMC")
@click.argument('file')
@click.option('-p', '--parallelism', type=int, default=2, help="has to be a power of two larger than one")
@click.option('--amc_epsilon', type=float, default=0.2)
@click.option('--amc_delta', type=float, default=0.8)
@click.option('--amc_forcesolextension', type=bool, default=False)
@click.option("-v", "--verbose", type=bool, default=False)
@click.option("--epsilon", type=float, default=0.2, help="Not yet implemented")
@click.option("--delta", type=float, default=0.8, help="Not yet implemented")
@click.option("--random", default=lambda: os.urandom(100))
@click.option("--iterations", type=int, default=5, help="number of loop iterations")
def cli(file, parallelism, amc_epsilon, amc_delta, amc_forcesolextension, verbose,
        epsilon, delta, random, iterations):
    import warnings
    warnings.warn("--epsilon and --delta don't have any effect currently")
    state = State.from_dcnf(DCNF.load(Path(file)),
                            Config(parallelism=parallelism,
                                   amc_epsilon=amc_epsilon,
                                   amc_delta=amc_delta,
                                   amc_forcesolextension=amc_forcesolextension,
                                   log_iterations=verbose,
                                   epsilon=epsilon,
                                   delta=delta))
    random_seed(random)
    ret = state.compute_loop(iterations)
    if ret >= 0:
        print(f"c count {ret}")
    else:
        print(f"c unsatisfiable")


if __name__ == '__main__':
    cli()
