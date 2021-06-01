import logging
import math
import multiprocessing
from dataclasses import dataclass, field
from statistics import median
from typing import Tuple, Set, List, Optional, Iterable,  Callable

from pysat.formula import CNF

from dsharpy.formula import count_sat, DCNF, sat, CNFGraph, Dep, trim_dcnf, \
    XORGenerator, XORs, FullyRandomXORGenerator, RelatedDeps
from dsharpy.stats import CountResult, Ps, EpsilonDelta, PriorDepKnowledge, DepOrder


@dataclass(frozen=True)
class Config:
    parallelism: int = -1
    """ -1: use all cpus """
    amc_epsilon: float = 0.8
    amc_delta: float = 0.2
    log_iterations: bool = True
    epsilon: float = 0.8
    delta: float = 0.2
    check_xor_variability: bool = True
    """ Check that the added xors lead to the variables having the desired variability in the rest of the program,
        use the xors that are nearest to desired variability """
    max_xor_retries: int = 10
    """ sufficiently large… """
    xor_generator: XORGenerator = field(default_factory=FullyRandomXORGenerator)
    trim: bool = True
    use_mis: bool = False
    """ Use meelgroup/mis to reduce the ind sets for model counting,
        doesn't seem to improve the results, only slows the analysis down by a factor > 2 """
    variability_in_all_places: bool = True   # todo: find better name
    """
    don't fixate variables, but add the XOR constraints for each dep.ret on every count
    essentially: use the algorithm described in the tech report
    """
    adhere_to_guarantees: bool = True
    """ Slows it down """
    shuffle_dep_order: bool = False

    @property
    def actual_parallelism(self) -> int:
        return self.parallelism if self.parallelism > 0 else multiprocessing.cpu_count()

    def __post_init__(self):
        assert self.parallelism > 0 or self.parallelism == -1

    @property
    def guarantees(self) -> EpsilonDelta:
        return EpsilonDelta(self.epsilon, self.delta)

    @property
    def initial_amc_guarantees(self) -> EpsilonDelta:
        return EpsilonDelta(self.amc_epsilon, self.amc_delta)


@dataclass
class _ComputeIter:
    """
    Externalizes the compute iterations for a given state, used by the method
    count_sat_fully. It is used to implement a parallel version.
    """

    cnf: CNF
    guarantees: EpsilonDelta
    parallelism: int
    """ 1 == no parallelism """
    iterations: int
    """ number of iterations """
    state: "State"
    """ state that offers the prev_counts """
    combination_func: Callable[[Iterable[float]], float] = median

    def compute(self) -> float:
        l: List[float] = []
        if self.parallelism == 1 or self.iterations == 1:
            for i in range(self.iterations):
                l.append(self._count_sat_fully_iter())
        else:
            with multiprocessing.Pool(self.parallelism) as pool:
                l = list(pool.map(self._count_sat_fully_iter, range(self.iterations)))
        return self.combination_func(l)

    def _count_sat_fully_iter(self, *args) -> float:
        cnf_copy = self.cnf.copy()
        for p in self.state.prev_counts:
            cnf_copy.extend(
                self.state.create_random_xor_clauses_possibly_checked(p.dep.ret, float(p)).to_dimacs(self.cnf.nv + 1))
        res = self.state.count_sat(cnf_copy)
        return res or 0


class State:

    def __init__(self, cnf: DCNF, config: Config = None, dep_relations: RelatedDeps = None,
                 prior_knowledge: PriorDepKnowledge = None,
                 prev_counts: Ps = Ps()):
        self.cnf = cnf
        self.config = config or Config()
        self.prev_counts: Ps = prev_counts
        self.logger = logging.getLogger("counter")
        self.dep_relations = (dep_relations or RelatedDeps(cnf).limited()).limited()
        self.prior_knowledge = prior_knowledge
        self.sub_guarantees = self.config.initial_amc_guarantees
        if not prior_knowledge and self.config.adhere_to_guarantees:
            self.prior_knowledge = PriorDepKnowledge.create(self.dep_relations,
                                                            lambda ind, con: self.count_sat(self.cnf, ind, con),
                                                            self.config.initial_amc_guarantees)

    def can_split(self) -> bool:
        return len(self.cnf.deps) > 0

    def create_dep_order(self) -> DepOrder:
        """
        Choose a single declared dependency.

        TODO: choose randomly?

        From a QIFC point of view, where the deps are generated (hopefully) in the order of their occurrence in the
        program, using the first dep of the list is probably useful
        """
        return DepOrder.create(self.cnf, self.config.shuffle_dep_order)

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
            self.config, self.dep_relations, self.prior_knowledge, self.prev_counts)  # dep relations don't change
        return CNFGraph(header_cnf).sub_cnf(), remaining_state

    def split(self, dep_order: DepOrder = None) -> Tuple[Dep, CNF, "State"]:
        """ see split_at """
        dep_order = dep_order or DepOrder(self.cnf.deps, self.cnf.ind)
        return (dep := next(dep_order)), *self.split_at(dep)

    @classmethod
    def from_string(cls, string: str, config: Config = None) -> 'State':
        return State(DCNF.load_string(string), config or Config())

    def count_sat(self, cnf: CNF, ind: Set[int] = None, constraints: Set[int] = None, guarantees: EpsilonDelta = None)\
            -> Optional[float]:
        guarantees = guarantees or self.config.initial_amc_guarantees
        if ind is None and constraints is None:
            return self._count_sat(cnf, guarantees)
        dcnf = DCNF(from_clauses=cnf.clauses)
        if constraints:
            dcnf.extend([[c] for c in constraints])
        return self._count_sat(dcnf.set_ind(ind), guarantees)

    def _count_sat(self, cnf: CNF, guarantees: EpsilonDelta = None) -> Optional[float]:
        guarantees = guarantees or self.config.initial_amc_guarantees
        return count_sat(cnf, epsilon=guarantees.epsilon,
                         delta=guarantees.delta,
                         trim=self.config.trim, use_mis=self.config.use_mis)

    def _compute_iterations(self, guarantees: EpsilonDelta) -> int:
        return math.ceil(35 * math.log2(3/guarantees.delta)) if self.config.adhere_to_guarantees else 1


    def count_sat_fully(self, cnf: CNF, parallelism: int = None, guarantees: EpsilonDelta = None) -> float:
        """ Count SAT with prev_counts to XORs if present """
        parallelism = parallelism or self.config.actual_parallelism
        guarantees = guarantees or self.config.initial_amc_guarantees
        if not self.config.variability_in_all_places or not self.prev_counts:
            return self._count_sat(cnf)
        return _ComputeIter(cnf, guarantees, parallelism, self._compute_iterations(guarantees), self).compute()

    def compute(self, parallelism: int = None) -> float:
        return float(self.compute_result(parallelism=parallelism))

    def compute_result(self, parallelism: int = None, dep_order: DepOrder = None,
                       sub_guarantees: EpsilonDelta = None) -> CountResult:
        """ Approximately compute the model count with respect to the dependencies """
        parallelism = parallelism or self.config.actual_parallelism

        dep_order = dep_order or self.create_dep_order()

        if self.config.adhere_to_guarantees and not sub_guarantees:
            # compute the sub delta and epsilon
            sub_guarantees = self.prior_knowledge.required_delta_and_epsilon(dep_order, self.config.guarantees)
            print(f"sub guarantees have to be ε={sub_guarantees.epsilon} and ẟ={sub_guarantees.delta} "
                             f"(results in {self._compute_iterations(sub_guarantees)} rounds each)")
        sub_guarantees = sub_guarantees or self.config.initial_amc_guarantees

        if not self.can_split():
            """ no splitting needed, ends the recursion """
            count = self.count_sat_fully(self.cnf, parallelism=parallelism, guarantees=sub_guarantees)
            return self.prev_counts.wrap(count, sub_guarantees,
                                         self.dep_relations.related_deps(self.cnf.ind))
        dep, cnf, new_state = self.split(dep_order)
        if self.config.variability_in_all_places:
            self.logger.info(f"computing {dep} under the constraint of {[math.log2(float(p)) for p in self.prev_counts]}")
        available_variability: float = min(dep.max_variability_of_ret(),
                                           float("inf")
                                           if dep.fully_over_approximate
                                           else self.count_sat_fully(cnf, parallelism=parallelism,
                                                                     guarantees=sub_guarantees))

        if available_variability == 0:  # this is most likely due to the constraints being unsatisfiable
            assert not sat(cnf)
            return new_state.compute_result(parallelism, dep_order, sub_guarantees)
        if self.config.variability_in_all_places:
            new_state.prev_counts = new_state.prev_counts.record(dep, available_variability,
                                                                 sub_guarantees,
                                                                 self.dep_relations.deps_related_to_dep(dep))
        else:
            new_state.cnf.extend(self.create_random_xor_clauses_possibly_checked(dep.ret, available_variability,
                                                                                 sub_guarantees=sub_guarantees)
                                 .to_dimacs(self.cnf.nv + 1))

        return new_state.compute_result(parallelism=parallelism, dep_order=dep_order, sub_guarantees=sub_guarantees)

    def create_random_xor_clauses_possibly_checked(self, variables: Iterable[int], available_variability: float,
                                                   sub_guarantees: EpsilonDelta = None) -> XORs:
        sub_guarantees = sub_guarantees or self.config.initial_amc_guarantees
        self.logger.info(f"{variables} (variability: {math.log2(available_variability):.2f} bits")
        if self.config.check_xor_variability:
            constraints = self.create_random_xor_clauses_checked(variables, available_variability, sub_guarantees)
        else:
            constraints = self.create_random_xor_clauses(variables, available_variability)
        self.logger.info(f"constraints: {constraints}")
        print(f"constraints {constraints}")
        return constraints

    def create_random_xor_clauses(self, variables: Iterable[int], available_variability: float) -> XORs:
        """
        Create an xor clause that restricts the variable of the passed vars to the available variability
        (on average)
        """
        return self.config.xor_generator.generate(list(variables), available_variability)

    def create_random_xor_clauses_checked(self, variables: Iterable[int], available_variability: float,
                                          sub_guarantees: EpsilonDelta) -> XORs:
        assert self.config.max_xor_retries > 0
        # only use the xor clauses if they lead to a satisfying variability
        count = 0
        possible_constraints: List[Tuple[float, XORs]] = []
        current_constraints = self.create_random_xor_clauses(variables, available_variability)
        while True:
            # todo: unsure whether or not using the cnf and constraints here would be appropriate, I tend to think not
            var = self.count_sat(CNF(from_clauses=current_constraints.to_dimacs(self.cnf.nv + 1)), ind=set(variables),
                                 guarantees=sub_guarantees)
            if (var is None and available_variability == 0) or (var is not None and round(var) == round(available_variability)):
                variability, constraints = var, current_constraints
                break
            if count >= self.config.max_xor_retries:
                # find the best constraint
                variability, constraints = min(possible_constraints, key=lambda t: abs(t[0] - available_variability))
                break
            possible_constraints.append((var, current_constraints))
            current_constraints = self.create_random_xor_clauses(variables, available_variability)
            count += 1
        #self.logger.info(
        #    f"# choosing {math.log2(variability) if var != 0 else 'unsat'} vs {available_variability}")
        return constraints

    def _compute_loop_iter(self, num: int, sub_parallelism: int = 1) -> float:
        count = self.compute(parallelism=sub_parallelism)
        if self.config.log_iterations:
            self.logger.info(f"-- run {num:2d}: {count:3f}")
        return count

    def compute_loop(self, iterations: int) -> float:
        if iterations == 1 or self.config.actual_parallelism == 1:
            counts = list(map(lambda num: self._compute_loop_iter(num, self.config.actual_parallelism),
                              range(iterations)))
        else:
            with multiprocessing.Pool(self.config.actual_parallelism) as p:
                counts = list(p.map(self._compute_loop_iter, range(iterations)))
        return max(counts)
