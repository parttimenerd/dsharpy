import math
import os
import shutil
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from random import random
from statistics import median
from tempfile import TemporaryDirectory
from typing import Tuple, Set, List, Dict, Optional, Union, cast, Iterable

import click as click
from prettyprinter import register_pretty, pretty_call
from pysat.formula import CNF

from dsharpy.formula import Independents, count_sat, DCNF, sum_is_one2, sum_is_one4, sat, CNFGraph, Dep, \
    trim_dcnf_graph, trim_dcnf, blast_xor, XOR
from dsharpy.util import random_exact_split, random_choice, pprint, random_seed, process_with_cbmc, has_modified_cbmc, \
    process_path_with_cbmc


@dataclass
class Config:
    parallelism: int = 2
    amc_epsilon: float = 0.8
    amc_delta: float = 0.2
    amc_forcesolextension: bool = False
    log_iterations: bool = False
    epsilon: float = 0.2
    delta: float = 0.8
    check_xors_for_variability: bool = False
    """ Check that the added xors lead to the variables having the desired variability in the rest of the program """

    def __post_init__(self):
        rel = math.log2(self.parallelism)
        assert int(rel) == math.ceil(rel) and rel >= 1


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
        return next(iter(self.cnf.deps.items()))

    def split_at(self, dep: Dep) -> Tuple[CNF, "State"]:
        """
        Splits the current cnf at dep  a ~> b

        :return cnf that depends on a (for which ind is a),
        """
        a_s, bs = dep
        header_cnf = CNF()
        header_cnf.from_clauses(self.cnf.clauses)
        header_cnf.comments = [DCNF.format_ind_comment(a_s)]
        remaining_state = State(
            trim_dcnf(self.cnf.set_deps({idep[0]: idep[1] for idep in self.cnf.deps.items() if dep != idep})),
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
                         forcesolextension=self.config.amc_forcesolextension)

    def create_random_xor_clause(self, vars: Iterable[int]) -> XOR:
        """ Create an xor clause that halves the variability of the passed vars (on average) """
        chosen = [(-1 if random() < 0.5 else 1) * v for v in vars if random() <= 0.5]
        return XOR(chosen)

    def create_random_xor_clauses(self, vars: Iterable[int], available_variability_bits: int) -> List[XOR]:
        """ Create an xor clause that restricts the variable of the passed vars to 2^{passed bits} (on average) """
        ret = []
        restricted_bits = len(list(vars)) - available_variability_bits
        for i in range(restricted_bits):
            ret.append(self.create_random_xor_clause(vars))
        return ret

    def approximate_variability_of_clauses(self, cnf: DCNF, new_clauses: List[List[int]], ind: Iterable[int]) -> float:
        new_cnf = CNF(from_clauses=cnf.clauses + new_clauses)
        new_cnf.comments = [DCNF.format_ind_comment(ind)]
        return self._count_sat(new_cnf)

    def compute(self) -> float:
        """ Approximately compute the model count with respect to the dependencies """
        if not self.can_split():
            """ no splitting needed, ends the recursion """
            return self._count_sat(self.cnf)
        (a_s, bs), cnf, new_state = self.split()
        available_variability = self._count_sat(cnf)
        # we over approximate the variability
        available_variability_bits_upper = math.ceil(math.log2(available_variability))
        print(f"{a_s} ~> {bs} (variability: {math.log2(available_variability):.2f} bits)")
        constraints: List[XOR] = self.create_random_xor_clauses(bs,
                                                                available_variability_bits_upper)  # TODO: more random
        print("constraints: " + "; ".join(map(str, constraints)))
        new_clauses = XOR.multiple_to_dimacs(constraints)

        if self.config.check_xors_for_variability:
            # only use the xor clauses if they lead to a satisfying variability
            # Todo: this might never end
            print(f"# {self.approximate_variability_of_clauses(new_state.cnf, new_clauses, bs)}")
            while self.approximate_variability_of_clauses(new_state.cnf, new_clauses, bs) != 2 ** min(len(bs),
                                                                                                      available_variability_bits_upper):
                print(
                    f"# {math.log2(self.approximate_variability_of_clauses(new_state.cnf, new_clauses, bs))} vs {available_variability_bits_upper}")
                new_clauses = XOR.multiple_to_dimacs(
                    self.create_random_xor_clauses(bs, available_variability_bits_upper))

        new_state.cnf.extend(new_clauses)
        return new_state.compute()

    def compute_loop(self, iterations: int) -> float:
        if not sat(self.cnf):
            return -1
        counts: List[float] = []
        for run in range(iterations):
            count = self.compute()
            counts.append(count)
            if self.config.log_iterations:
                print(f"-- run {run:2d}: {count:3f}     median = {median(counts):3f}  max = {max(counts):3f}")

        return max(counts)


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
@click.option('-p', '--parallelism', type=int, default=2, help="has to be a power of two larger than one")
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
