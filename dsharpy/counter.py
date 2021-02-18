import math
import multiprocessing
import os
import shutil
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from statistics import median
from typing import Tuple, Set, List, Optional, Union, Iterable

import click as click
from pysat.formula import CNF

from dsharpy.formula import count_sat, DCNF, sat, CNFGraph, Dep, trim_dcnf, \
    RangeSplitXORGenerator, XORGenerator, XORs
from dsharpy.util import random_seed, has_modified_cbmc, process_path_with_cbmc


@dataclass(frozen=True)
class Config:
    parallelism: int = -1
    """ -1: use all cpus """
    amc_epsilon: float = 0.8
    amc_delta: float = 0.2
    amc_forcesolextension: bool = False
    log_iterations: bool = True
    epsilon: float = 0.2
    delta: float = 0.8
    check_xors_for_variability: bool = True
    """ Check that the added xors lead to the variables having the desired variability in the rest of the program """
    xor_generator: XORGenerator = field(default_factory=RangeSplitXORGenerator)
    trim: bool = True

    @property
    def actual_parallelism(self) -> int:
        return self.parallelism if self.parallelism > 0 else multiprocessing.cpu_count()

    def __post_init__(self):
        assert self.parallelism > 0 or self.parallelism == -1


class State:

    def __init__(self, cnf: DCNF, config: Config = None):
        self.cnf = cnf
        self.config = config or Config()

    def can_split(self) -> bool:
        return len(self.cnf.deps) > 0

    def choose_dep(self) -> Dep:
        """
        Choose a single declared dependency.

        TODO: choose randomly?

        From a QIFC point of view, where the deps are generated (hopefully) in the order of their occurrence in the
        program, using the first dep of the list is probably useful
        """
        return self.cnf.deps[0]

    def split_at(self, dep: Dep) -> Tuple[CNF, "State"]:
        """
        Splits the current cnf at dep  a ~> b

        :return cnf that depends on a (for which ind is a),
        """
        header_cnf = CNF()
        header_cnf.from_clauses(self.cnf.clauses)
        header_cnf.comments = [DCNF.format_ind_comment(dep.param)]
        header_cnf.nv = max(header_cnf.nv, max(dep.param, default=0))
        for guard in dep.constraint:
            header_cnf.append([guard])
        remaining_state = State(
            trim_dcnf(self.cnf.set_deps([idep for idep in self.cnf.deps if dep != idep])),
            self.config)
        return CNFGraph(header_cnf).sub_cnf(), remaining_state

    def split(self) -> Tuple[Dep, CNF, "State"]:
        """ see split_at """
        return (dep := self.choose_dep()), *self.split_at(dep)

    @classmethod
    def from_string(cls, string: str, config: Config = None) -> 'State':
        return State(DCNF.load_string(string), config or Config())

    def count_sat(self, cnf: CNF, ind: Set[int]) -> Union[List[Optional[float]], Optional[float]]:
        """ Helpful for debugging """
        dcnf = DCNF(from_clauses=cnf.clauses)
        return self._count_sat(dcnf.set_ind(ind))

    def _count_sat(self, cnf: Union[List[CNF], CNF]) -> Union[List[Optional[float]], Optional[float]]:
        return count_sat(cnf, epsilon=self.config.amc_epsilon,
                         delta=self.config.amc_delta,
                         forcesolextension=self.config.amc_forcesolextension,
                         trim=self.config.trim)

    def create_random_xor_clauses(self, variables: Iterable[int], available_variability: float) -> XORs:
        """ Create an xor clause that restricts the variable of the passed vars to 2^{passed bits} (on average) """
        return self.config.xor_generator.generate(list(variables), available_variability)

    def approximate_variability_of_clauses(self, cnf: DCNF, new_clauses: List[List[int]], ind: Iterable[int],
                                           constraints: Set[int] = None) -> float:
        new_cnf = CNF(from_clauses=cnf.clauses + new_clauses + [[constraint] for constraint in (constraints or [])])
        new_cnf.nv = max(cnf.nv, new_cnf.nv)
        new_cnf.comments = [DCNF.format_ind_comment(ind)]
        return self._count_sat(new_cnf)

    def compute(self) -> float:
        """ Approximately compute the model count with respect to the dependencies """
        if not self.can_split():
            """ no splitting needed, ends the recursion """
            return self._count_sat(self.cnf)
        dep, cnf, new_state = self.split()
        available_variability: float = 2 ** min(len(dep.param),
                                                len(dep.ret)) if dep.fully_over_approximate else self._count_sat(cnf)

        if available_variability == 0:  # this is most likely due to the constraints being unsatisfiable
            assert not sat(cnf)
            return new_state.compute()

        # we overapproximate the variability
        max_variability_bits = math.log2(dep.max_variability) if dep.max_variability else float("inf")
        available_variability_bits = min(math.log2(available_variability), max_variability_bits)
        print(f"{dep} (variability: {available_variability_bits:.2f} (max_var: {max_variability_bits:.2f}) bits)")
        constraints: XORs = self.create_random_xor_clauses(dep.ret, available_variability_bits)
        print(f"constraints: {constraints}")
        new_clauses = constraints.to_dimacs(self.cnf.nv + 1)

        if self.config.check_xors_for_variability:
            # only use the xor clauses if they lead to a satisfying variability
            # Todo: this might never end
            count = 0
            while count < 10 and (var := self.approximate_variability_of_clauses(new_state.cnf, new_clauses, dep.ret,
                                                                                 dep.constraint)) != 2 ** min(
                len(dep.ret),
                math.ceil(available_variability_bits)):
                print(f"# {math.log2(var) if var != 0 else 'unsat'} vs {available_variability_bits}")
                new_clauses = self.create_random_xor_clauses(dep.ret, available_variability_bits).to_dimacs(
                    self.cnf.nv + 1)
                count += 1
        new_state.cnf.extend(new_clauses)
        return new_state.compute()

    def _compute_loop_iter(self, num: int) -> float:
        count = self.compute()
        if self.config.log_iterations:
            print(f"-- run {num:2d}: {count:3f}")
        return count

    def compute_loop(self, iterations: int) -> float:
        counts: List[float] = []
        with multiprocessing.Pool(self.config.actual_parallelism) as p:
            counts = list(p.map(self._compute_loop_iter, range(iterations)))
        return median(counts)


@dataclass
class PathWrapper:
    path: Path
    base: Optional[Path] = None

    def __del__(self):
        if self.base:
            shutil.rmtree(self.base)


def convert_if_necessary(ctx: click.Context, param: str, value: str) -> PathWrapper:
    file = Path(value)
    if file.suffix in [".c", ".cpp"]:
        if not has_modified_cbmc():
            raise BaseException("Install modified CBMC via update.sh")
        temp = Path(tempfile.mkdtemp())
        return PathWrapper(process_path_with_cbmc(file, temp), temp)
    return PathWrapper(file)


@click.command(name="dsharpy", help="""An approximate model counter with dependencies based on ApproxMC

Supports DCNF and C/CPP files (if the modified CBMC is installed)
""")
@click.argument('file', type=click.Path(exists=True), callback=convert_if_necessary)
@click.option('-p', '--parallelism', type=int, default=-1, help="-1: use system parallelism, > 0: level of parallelism, other values are unsupported")
@click.option('--amc_epsilon', type=float, default=0.2)
@click.option('--amc_delta', type=float, default=0.8)
@click.option('--amc_forcesolextension', type=bool, default=False)
@click.option("-v", "--verbose", type=bool, default=False)
@click.option("--epsilon", type=float, default=0.2, help="Not yet implemented")
@click.option("--delta", type=float, default=0.8, help="Not yet implemented")
@click.option("--random", default=lambda: os.urandom(100))
@click.option("--iterations", type=int, default=5, help="number of loop iterations")
def cli(file: PathWrapper, parallelism, amc_epsilon, amc_delta, amc_forcesolextension, verbose,
        epsilon, delta, random, iterations):
    import warnings
    warnings.warn("--epsilon and --delta don't have any effect currently")
    state = State(DCNF.load(file.path),
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
