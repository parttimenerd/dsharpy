"""
Build abstract versions of loops and recursion, to find basic invariants that can be used to improve the leakage
computation.

Currently with only recursion abstractions, as loop abstraction is far more difficult
(and not done in my masters thesis) and doesn't seem to have that much benefit
in relation with the required effort.
"""
from abc import abstractmethod, ABC
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import List, Mapping, Iterator, Dict, Set, MutableMapping, Optional, Callable, Deque, Iterable, FrozenSet, \
    Tuple, Union

from dsharpy.formula import Deps, Dep, count_sat, DCNF

Clause = List[int]
Clauses = List[Clause]

Variable = Union[int, bool]
""" variables might be all integers except 0 and booleans """

Variables = List[Variable]

IntToVariableMap = MutableMapping[int, Variable]

VariableMap = MutableMapping[Variable, Optional[Variable]]


def is_constant(var: Variable) -> bool:
    return var is True or var is False


def parse_variable(var: str) -> Variable:
    assert var != "0"
    return int(var) if var.isnumeric() or var[0] == "-" else bool(var)


def to_abs_variables(variables: Variables) -> List[int]:
    """ Filters boolean and removes negations """
    return [abs(v) for v in variables if not is_constant(v)]


def get_vars(clauses: Clauses) -> Set[int]:
    return set(abs(v) for clause in clauses for v in clause)


def create_mapping(vars: Set[int], new_start: int = 0, keep: List[int] = None,
                   custom_mapping: IntToVariableMap = None) -> IntToVariableMap:
    """
    Create a mapping of each of the variables to a new variables

    :param new_start: start variable for new variables
    :param keep: keep the passed variables unchanged
    :param custom_mapping: keep these mappings (overriden by keep)
    :return a mapping that contains the variables
    """
    ret = dict(custom_mapping) if custom_mapping else dict()
    if keep:
        ret.update({k: k for k in keep})
    variables_not_in_custom_mapping = sorted(vars.difference(ret.keys()))
    for var in variables_not_in_custom_mapping:
        ret[var] = new_start
        new_start += 1
    return ret


def negate(var: Variable) -> Variable:
    return not var if is_constant(var) else -var


def transpose_single(var: int, mapping: IntToVariableMap) -> Variable:
    if var < 0:
        return negate(transpose_single(-var, mapping))
    return mapping[var]


def transpose_clauses(clauses: Clauses, mapping: IntToVariableMap) -> Clauses:
    ret: Clauses = []
    for clause in clauses:
        new_clause = []
        for x in clause:
            n = transpose_single(x, mapping)
            if n is True:  # the clause is True and can therefore be omitted
                new_clause = [True]
                break
            if n is False:
                return [[]]  # this clause cannot be satisfied
            new_clause.append(n)
        if new_clause != [True]:
            ret.append(new_clause)
    return ret


@dataclass(frozen=True)
class NameMapping(Mapping[str, Variables]):
    base: Dict[str, Variables]

    def __getitem__(self, name: str) -> Clause:
        return self.base[name]

    def __len__(self) -> int:
        return len(self.base)

    def __iter__(self) -> Iterator[str]:
        return iter(self.base)

    def transpose(self, mapping: IntToVariableMap) -> "NameMapping":
        return NameMapping({name: [transpose_single(v, mapping) for v in c] for name, c in self.base.items()})

    def check(self, other: "NameMapping") -> bool:
        for name in self.base:
            if name not in other.base:
                return False
            c1, c2 = self[name], other[name]
            if len(c1) != len(c2):
                return False
            if any(v1 == 0 and v2 != 0 for v1, v2 in zip(c1, c2)):
                return False
        for name in other.base:
            if name not in self.base:
                return False
        return True

    def create_mapping(self, other: "NameMapping") -> VariableMap:
        """ Create a mapping that maps all sat variables from this map to the ones of the other map """
        ret: VariableMap = {}
        for name in self.base:
            ret.update({i1: i2 for i1, i2 in zip(self.base[name], other.base[name])})
        return ret

    def combined_clause(self) -> Clause:
        """ omits contant variables """
        return [x for variables in self.base.values() for x in to_abs_variables(variables)]

    def __str__(self):
        return str(self.base)


def transpose_dep(dep: Dep, mapping: IntToVariableMap) -> Optional[Dep]:
    """ Transpose the dep, returns False if the dep is obsolete (a constraint is False) """

    def transpose_set(s: FrozenSet[int]) -> FrozenSet[int]:
        return frozenset(abs(new_v) for v in s if not is_constant(new_v := transpose_single(v, mapping)))

    new_constraint = []
    for v in dep.constraint:
        new_v = transpose_single(v, mapping)
        if new_v is False:
            return None
        if new_v is not True:
            new_constraint.append(new_v)
    return Dep(transpose_set(dep.param), transpose_set(dep.ret), frozenset(new_constraint), dep.max_variability)


def transpose_deps(deps: Deps, mapping: VariableMap) -> Deps:
    """ Removes obsolete deps """
    return [new_dep for dep in deps if (new_dep := transpose_dep(dep, mapping)) and not new_dep.empty()]


VariabilityEstimator = Callable[[DCNF], float]
""" 
Estimates (and over approximates) the variability of a given CNF with and 'ind' line
and deps
"""


@dataclass
class ApplicableCNF:
    """
    An abstract function, declared in CNF, that can be applied
    """

    input: NameMapping
    """ positive integers, 0 means that a SAT variable can safely be ignored """
    output: NameMapping
    clauses: Clauses
    deps: Deps
    misc_vars: NameMapping = field(default_factory=lambda: NameMapping({}))

    def _check_clauses(self) -> "ApplicableCNF":
        """ Check that clauses contain don't contain constants """
        if any(is_constant(x) or x is None for clause in self.clauses for x in clause):
            raise AssertionError("Clauses contain constant")
        return self

    def add_deps(self, deps: Deps) -> "ApplicableCNF":
        return ApplicableCNF(self.input, self.output, self.clauses, self.deps + deps, self.misc_vars)

    def add_clauses(self, clauses: Clauses) -> "ApplicableCNF":
        return ApplicableCNF(self.input, self.output, self.clauses + clauses, self.deps, self.misc_vars)

    def transpose(self, new_start: int, keep: List[int] = None,
                  custom_mapping: IntToVariableMap = None) -> "ApplicableCNF":
        mapping = create_mapping(self.get_vars(), new_start, keep, custom_mapping)
        return ApplicableCNF(self.input.transpose(mapping), self.output.transpose(mapping),
                             transpose_clauses(self.clauses, mapping), transpose_deps(self.deps, mapping),
                             self.misc_vars.transpose(mapping))

    def get_vars(self) -> Set[int]:
        ret = get_vars(self.clauses)
        for dep in self.deps:
            for l in [dep.param, dep.ret, dep.constraint]:
                ret.update(abs(v) for v in l)
        return ret

    def apply(self, new_start: int, input: NameMapping, output: Optional[NameMapping]) -> "ApplicableCNF":
        """
        Applies the CNF to the passed input mapping, after transposing the formula
        :param output: an empty name mapping is equivalent to: create new variables
        :return: applied formula
        """
        if not self.input.check(input):
            raise AssertionError(f"Input mappings are invalid: {input} vs {self.input}")
        if output and not self.output.check(output):
            raise AssertionError(f"Output mappings are invalid: {output} vs {self.output}")
        mapping = self.input.create_mapping(input)
        if output:
            mapping.update(self.output.create_mapping(output))
        return self.transpose(new_start, custom_mapping=mapping)._check_clauses()

    def to_cnf(self) -> DCNF:
        cnf = DCNF(from_clauses=self.clauses)
        return cnf.set_deps(self.deps)

    def count_sat(self, estimator: VariabilityEstimator = count_sat) -> float:
        return estimator(self.to_cnf().set_ind(self.output.combined_clause()))

    def max_var(self) -> int:
        return max(self.get_vars())


@dataclass
class RecursionChild:
    node_store: Dict[str, "RecursionNode"]
    id: int
    node_id: str
    input: NameMapping
    output: NameMapping
    constraint: Set[int]

    @property
    def node(self) -> "RecursionNode":
        return self.node_store[self.node_id]

    def __hash__(self):
        return self.id

    def __eq__(self, other):
        return other.id == self.id


class RecursionNode:
    """
    A node in the recursion graph
    """

    def __init__(self, id: str, acnf: ApplicableCNF, children: List[RecursionChild]):
        """
        Constructor

        :param id: name of the function (just a unique id used for comparison and hashing)
        :param acnf: the cnf of this recursion node with inputs, outputs and non recursive deps
        :param children: recursive calls that lead to aborted recursion in this node
        """
        self.id = id
        self.acnf = acnf
        self.children = children

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        return other.id == self.id

    def child_nodes(self) -> Iterable["RecursionNode"]:
        return (child.node for child in self.children)

    def to_applicable(self,
                      child_to_dep: Callable[[RecursionChild, Callable[[], int]], Union[Dep, Tuple[Dep, Clauses]]] =
                      lambda c, n: Dep(frozenset(c.input.combined_clause()), frozenset(c.output.combined_clause()),
                                       frozenset(c.constraint))) \
            -> ApplicableCNF:
        """ Create an applicable cnf that includes all deps from children """
        max_var = [0]

        def new_id() -> int:
            max_var[0] = (max_var[0] or self.acnf.max_var()) + 1
            return max_var[0]

        deps = []
        all_clauses = []
        for child in self.children:
            dep_or_tuple = child_to_dep(child, new_id)
            if isinstance(dep_or_tuple, Dep):
                dep, clauses = dep_or_tuple, []
            else:
                dep, clauses = dep_or_tuple
            max_var[0] = max(max_var[0], dep.max_var(),
                             max(max(clause) if clause else 0 for clause in clauses) if clauses else 0)
            deps.append(dep)
            all_clauses.extend(clauses)
        acnf = self.acnf
        if all_clauses:
            acnf = self.acnf.add_clauses(all_clauses)
        return acnf.add_deps(deps)


def walk_recursion_nodes(start_nodes: List[RecursionNode], children: Callable[[RecursionNode], Iterable[RecursionNode]],
                         processor: Callable[[RecursionNode], bool]):
    """
    Fix point iteration on the recursion graph

    :param start_nodes: start nodes of the graph
    :param children: children of a node
    :param processor: processes each recursion node and return true iff something changed in its representation
    """
    parents: Dict[RecursionNode, Set[RecursionNode]] = defaultdict(set)

    worklist: Deque[RecursionNode] = deque()
    in_work_list: Set[RecursionNode] = set()

    def add(node: RecursionNode):
        if node not in in_work_list:
            worklist.append(node)
            in_work_list.add(node)

    def add_all(nodes: Iterable[RecursionNode]):
        for node in nodes:
            add(node)

    def pop() -> RecursionNode:
        node = worklist.pop()
        in_work_list.remove(node)
        return node

    def clear():
        worklist.clear()
        in_work_list.clear()

    # find parents

    add_all(start_nodes)
    visited: Set[RecursionNode] = set()
    while len(worklist):
        node = pop()
        if node in visited:
            continue
        visited.add(node)
        for child in children(node):
            parents[child].add(node)
            add(child)

    clear()

    # the actual fix point iteration

    add_all(visited)
    while len(worklist):
        node = pop()
        if processor(node):
            add_all(parents[node])


@dataclass
class RecursionProcessingResult:
    max_variability: Dict[RecursionNode, float] = field(default_factory=lambda: defaultdict(lambda: float("inf")))
    constraints: Dict[RecursionNode, Clauses] = field(default_factory=lambda: defaultdict(list))

    def to_applicable(self, node: RecursionNode) -> ApplicableCNF:
        def func(c: RecursionChild, n: Callable[[], int]):
            orig_dep = Dep(frozenset(c.input.combined_clause()),
                           frozenset(c.output.combined_clause()),
                           frozenset(c.constraint), self.max_variability[node])
            misc_cons = self.constraints[c.node]
            if misc_cons:
                new_id = max(n(), orig_dep.max_var() + 1)
                new_clauses = transpose_clauses(misc_cons, create_mapping(get_vars(misc_cons), new_id + 1))
                new_clauses_impl = [[-new_id] + clause for clause in new_clauses]
                return Dep(orig_dep.param, orig_dep.ret, frozenset((new_id, *orig_dep.constraint)),
                           orig_dep.max_variability), new_clauses
            return orig_dep

        return node.to_applicable(func)

    def update(self, node: RecursionNode, max_variability: float) -> bool:
        cur = self.max_variability[node]
        self.max_variability[node] = max_variability
        return cur != max_variability


class RecursionProcessor(ABC):

    @abstractmethod
    def run(self) -> RecursionProcessingResult:
        pass


class MaxVariabilityRecursionProcessor(RecursionProcessor):
    """ Estimates the maximum variability used in dependencies """

    def __init__(self, start_nodes: List[RecursionNode],
                 variability_estimator: VariabilityEstimator,
                 state: RecursionProcessingResult = None):
        self.start_nodes = start_nodes
        self.variability_estimator = variability_estimator
        self.state: RecursionProcessingResult = state or RecursionProcessingResult()

    def run(self) -> RecursionProcessingResult:
        walk_recursion_nodes(self.start_nodes, RecursionNode.child_nodes, self._process)
        return self.state

    def _process(self, node: RecursionNode) -> bool:
        return self.state.update(node, self._calculate_max_variability(node))

    def _calculate_max_variability(self, node: RecursionNode) -> float:
        return self.state.to_applicable(node).count_sat(self.variability_estimator)


class BitGraph:
    # todo: implement

    def compute(self, bit_graph_for_child: Callable[[str], "BitGraph"]):
        pass


class MaxVariabilityBitGraphRecursionProcessor(RecursionProcessor):
    """
    Same as MaxVariabilityRecursionProcessor, but uses bit graphs instead of a D#SAT counter.
    This has multiple advantages:
        - probably faster (but with larger memory requirements
        - surely sound (which the other isn't)
        - bit graphs can be reused as different model counter
    Disadvantages:
        - more work
        - less precision
    """

    def __init__(self, start_nodes: List[RecursionNode],
                 state: RecursionProcessingResult = None):
        self.start_nodes = start_nodes
        self.state: RecursionProcessingResult = state or RecursionProcessingResult()
        self.bit_graphs: Dict[str, BitGraph] = {}  # todo: create default bit graphs

    def run(self) -> RecursionProcessingResult:
        raise NotImplementedError()


class ConstraintRecursionProcessor(RecursionProcessor):
    """
    Tries to find constraints that each recursion enforces on the relation.
    Problem: hard to to do
    Preliminary ideas:
        - minimize aggressively (how?)
            - throw out random clauses
    """

    def run(self) -> RecursionProcessingResult:
        raise NotImplementedError()
