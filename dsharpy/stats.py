"""
Code that helps to keep track of the result guarantees
"""

import math
from dataclasses import dataclass, field
from functools import reduce
from typing import Tuple, FrozenSet, Dict, Iterator, List, Set, Callable, Iterable, Union

from dsharpy.formula import Dep, RelatedDeps, Ind, DCNF, LimitedRelatedDeps
from dsharpy.util import random_shuffle


class DepOrder:
    """ Order in which the dependencies are processed """

    def __init__(self, deps: List[Dep], ind: Ind, current_index: int = 0):
        self.deps = deps
        self.ind = ind
        self.current_index = current_index

    def __next__(self) -> "Dep":
        assert not self.empty()
        d = self.deps[self.current_index]
        self.current_index += 1
        return d

    def empty(self) -> bool:
        return self.current_index >= len(self.deps)

    def reset(self):
        self.current_index = 0

    def copy(self) -> "DepOrder":
        return DepOrder(list(self.deps), self.ind, self.current_index)

    def shuffle(self) -> "DepOrder":
        return DepOrder(random_shuffle(self.deps), self.ind, self.current_index)

    @classmethod
    def create(cls, cnf: DCNF, shuffle: bool = False) -> "DepOrder":
        return DepOrder(random_shuffle(cnf.deps) if shuffle else cnf.deps, cnf.ind)


@dataclass(frozen=True)
class CountResult:
    variability: float
    prob: float
    """ 1 - delta """
    range: Tuple[float, float]
    """ P[variability in range] >= prob, [lower, upper]"""

    def __post_init__(self):
        assert self.range[0] <= self.range[1]
        assert 0 <= self.prob <= 1

    def __float__(self) -> float:
        return float(self.variability)

    def __str__(self):
        return f"Pr[2^{math.log2(self.range[0]):.2f}, 2^{math.log2(self.range[1]):.2f}] >= 1 - {self.prob:.2f}"

    def __neg__(self) -> "CountResult":
        return CountResult(-self.variability, self.prob, (-self.range[1], -self.range[0]))

    @classmethod
    def create(cls, variability: float, prob: float, epsilon: float) -> "CountResult":
        """
        Asserts that Pr[[correct var] / (1 + e) <= variability <= (1 + e) [correct var]] >= prob
        """
        return CountResult(variability, prob, (variability / (1 + epsilon), variability * (1 + epsilon)))

    @property
    def lower_epsilon(self) -> float:
        return self.variability / self.range[0] - 1

    @property
    def upper_epsilon(self) -> float:
        return self.range[1] / self.variability - 1

    @property
    def epsilon(self) -> float:
        return max(self.lower_epsilon, self.upper_epsilon)


@dataclass(frozen=True)
class P:

    dep: Dep
    """ dep to use the returns of """
    variability: CountResult

    @property
    def variables(self) -> FrozenSet[int]:
        return self.dep.ret

    def __float__(self) -> float:
        return float(self.variability)


@dataclass(frozen=True)
class EpsilonDelta:
    epsilon: float
    delta: float

    @property
    def probability(self) -> float:
        return 1 - self.delta


@dataclass(frozen=True)
class Ps:

    ps: Dict[Dep, P] = field(default_factory=dict)

    def __iter__(self) -> Iterator[P]:
        return iter(self.ps.values())

    def wrap(self, variability: float, own_guarantees: EpsilonDelta, related_deps: Set[Dep]) -> CountResult:
        # todo
        own_epsilon, own_prob = own_guarantees.epsilon, own_guarantees.probability
        return CountResult(variability, own_prob, (variability / (1 + own_epsilon), variability * (1 + own_epsilon))) # todo: take related into account

    def record(self, dep: Dep, variability: float, own_guarantees: EpsilonDelta, related_deps: Set[Dep]) -> "Ps":
        return Ps({**self.ps, dep: P(dep, self.wrap(variability, own_guarantees, related_deps))})


class PriorDepKnowledge:
    """
    Allows to approximate the required sub prob and epsilon.

    Main interface to this class:
        - create(…)
        - required_delta_and_epsilon(…)
        - dep_max    maximum with (epsilon, delta)
        - ind_max
    """

    def __init__(self, dep_relations: LimitedRelatedDeps, dep_max: Dict[Dep, float], ind_max: float, guarantees: EpsilonDelta):
        self.dep_relations = dep_relations
        self.dep_max = dep_max
        self.ind_max = ind_max
        self.guarantees = guarantees

    def compute_count_approx(self, dep_order: DepOrder, assume_epsilon: float = None) -> CountResult:
        """
        Each DHashCount:

            prob * prob for correctness of own result
            epsilon * epsilon for …

        :param dep_order:
        :param assume_epsilon: assume the passed epsilon, useful for approximating the needed epsilon
        :return:
        """
        dep_to_count: Dict[Dep, CountResult] = {}
        dep_order = dep_order.copy()
        epsilon = assume_epsilon or self.guarantees.epsilon

        def compute(val: float, related_deps: Set[Dep]) -> CountResult:
            related = [dep_to_count[d] for d in related_deps if d in dep_to_count]
            prob = reduce(lambda x, y: x * y,
                          [dep_to_count[d] for d in related_deps if d in dep_to_count and not d.fully_over_approximate],
                          self.guarantees.probability ** 2)
            # todo: keep an eye on fully over approx!!!
            l, h = []

            return CountResult(self.dep_max[dep], prob, (l, h))

        while not dep_order.empty():
            dep = next(dep_order)
            dep_to_count[dep] = compute(self.dep_max[dep], self.dep_relations.deps_related_to_dep(dep))
        return compute(self.ind_max, self.dep_relations.related_deps(dep_order.ind))

    def required_prob(self, ind_res: CountResult, desired_prob: float) -> float:
        times_prob_multiplied = math.log(ind_res.prob, self.guarantees.probability)
        return math.pow(desired_prob, 1 / times_prob_multiplied)

    def required_epsilon(self, dep_order: DepOrder, desired_epsilon: float, step_factor: float = 0.3) -> float:
        current_epsilon = self.guarantees.epsilon
        while self.compute_count_approx(dep_order, current_epsilon).epsilon > desired_epsilon:
            current_epsilon *= step_factor
        return current_epsilon

    def required_delta_and_epsilon(self, dep_order: DepOrder, desired: EpsilonDelta) -> EpsilonDelta:
        return EpsilonDelta(1 - self.required_prob(self.compute_count_approx(dep_order), desired.probability),
                            self.required_epsilon(dep_order, desired.epsilon))


    @classmethod
    def create(cls, dep_relations: Union[LimitedRelatedDeps, DCNF], compute: Callable[[Iterable[int], Iterable[int]], float],
               guarantees: EpsilonDelta) -> "PriorDepKnowledge":
        return PriorDepKnowledge(dep_relations if isinstance(dep_relations, LimitedRelatedDeps) else RelatedDeps(dep_relations).limited(),
                                 {dep: (compute(dep.param, dep.constraint)
                                        if not dep.fully_over_approximate
                                        else dep.max_variability_of_ret) for dep in dep_relations.dcnf.deps},
                                 compute(dep_relations.dcnf.ind, []), guarantees)
