import logging
import math
import multiprocessing
from dataclasses import dataclass, field
from statistics import median
from typing import Tuple, Set, List, Optional, Union, Iterable

from pysat.formula import CNF

from dsharpy.formula import count_sat, DCNF, sat, CNFGraph, Dep, trim_dcnf, \
    XORGenerator, XORs, FullyRandomXORGenerator


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
    check_xor_variability: bool = True
    """ Check that the added xors lead to the variables having the desired variability in the rest of the program,
        use the xors that are nearest to desired variability """
    max_xor_retries: int = 10
    xor_generator: XORGenerator = field(default_factory=FullyRandomXORGenerator)
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
        self.logger = logging.getLogger("counter")

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
        self.logger.info(f"{dep} (variability: {available_variability_bits:.2f} (max_var: {max_variability_bits:.2f}) bits)")
        constraints: XORs = self.create_random_xor_clauses(dep.ret, available_variability_bits)
        self.logger.info(f"constraints: {constraints}")
        new_clauses = constraints.to_dimacs(self.cnf.nv + 1)

        if self.config.check_xor_variability:
            assert self.config.max_xor_retries > 0
            # only use the xor clauses if they lead to a satisfying variability
            count = 0
            possible_constraints: List[Tuple[float, XORs]] = []
            current_constraints = constraints
            expected_variability = 2 ** min(len(dep.ret), math.ceil(available_variability_bits))
            while True:
                var = self.approximate_variability_of_clauses(new_state.cnf,
                                                               current_constraints.to_dimacs(self.cnf.nv + 1),
                                                               dep.ret, dep.constraint)
                if var == expected_variability:
                    variability, constraints = var, current_constraints
                    break
                if count >= self.config.max_xor_retries:
                    # find the best constraint
                    variability, constraints = min(possible_constraints, key=lambda t: abs(t[0] - expected_variability))
                    break
                possible_constraints.append((available_variability_bits, current_constraints))
                current_constraints = self.create_random_xor_clauses(dep.ret, available_variability_bits)
                count += 1
            self.logger.info(f"# choosing {math.log2(variability) if var != 0 else 'unsat'} vs {available_variability_bits}")

        new_state.cnf.extend(constraints.to_dimacs(self.cnf.nv + 1))
        return new_state.compute()

    def _compute_loop_iter(self, num: int) -> float:
        count = self.compute()
        if self.config.log_iterations:
            self.logger.info(f"-- run {num:2d}: {count:3f}")
        return count

    def compute_loop(self, iterations: int) -> float:
        counts: List[float] = []
        if iterations == 1 or self.config.actual_parallelism:
            counts = list(map(self._compute_loop_iter, range(iterations)))
        else:
            with multiprocessing.Pool(self.config.actual_parallelism) as p:
                counts = list(p.map(self._compute_loop_iter, range(iterations)))
        return median(counts)
