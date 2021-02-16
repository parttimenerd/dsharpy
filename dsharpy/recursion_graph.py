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

from dsharpy.formula import Deps, Dep, count_sat, DCNF, IncrementalRelations
from dsharpy.util import DepGenerationPolicy

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

    :param vars: variables to map
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
    assert var in mapping or -var in mapping
    if var not in mapping:
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
    base: Dict[str, Variables] = field(default_factory=dict)

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

    def max_var(self) -> int:
        return max((abs(x) for variables in self.base.values() for x in to_abs_variables(variables)), default=0)

    def get_vars(self) -> Set[int]:
        return {abs(v) for v in self.combined_clause()}

    def values(self) -> Iterable[Variables]:
        return self.base.values()

    def __or__(self, other: "NameMapping") -> "NameMapping":
        assert all(name not in other.base for name in self.base)
        return NameMapping({**self.base, **other.base})


def transpose_dep(dep: Dep, param_mapping: IntToVariableMap, ret_mapping: IntToVariableMap = None,
                  constraint_mapping: IntToVariableMap = None) -> Optional[Dep]:
    """ Transpose the dep, returns False if the dep is obsolete (a constraint is False) """

    def transpose_set(s: FrozenSet[int], mapping: IntToVariableMap) -> FrozenSet[int]:
        return frozenset(abs(new_v) for v in s if not is_constant(new_v := transpose_single(v, mapping)))

    ret_mapping = ret_mapping or param_mapping
    constraint_mapping = constraint_mapping or param_mapping
    new_constraint = []
    for v in dep.constraint:
        new_v = transpose_single(v, constraint_mapping)
        if new_v is False:
            return None
        if new_v is not True:
            new_constraint.append(new_v)
    return Dep(transpose_set(dep.param, param_mapping), transpose_set(dep.ret, ret_mapping), frozenset(new_constraint),
               dep.max_variability)


def transpose_deps(deps: Deps, param_mapping: IntToVariableMap,
                   ret_mapping: IntToVariableMap = None,
                   constraint_mapping: IntToVariableMap = None) -> Deps:
    """ Removes obsolete deps """
    return [new_dep for dep in deps
            if (new_dep := transpose_dep(dep, param_mapping, ret_mapping, constraint_mapping)) and not new_dep.empty()]


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
        ret.update(self.input.get_vars())
        ret.update(self.output.get_vars())
        ret.update(self.misc_vars.get_vars())
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
        return max(self.get_vars(), default=0)


class DefaultApplicableCNF(ApplicableCNF):

    def __init__(self, input: NameMapping, output: NameMapping):
        super(DefaultApplicableCNF, self).__init__(input, output, [], [])

    def add_deps(self, deps: Deps) -> "ApplicableCNF":
        return self

    def add_clauses(self, clauses: Clauses) -> "ApplicableCNF":
        return self

    def transpose(self, new_start: int, keep: List[int] = None,
                  custom_mapping: IntToVariableMap = None) -> "ApplicableCNF":
        return self

    def apply(self, new_start: int, input: NameMapping, output: Optional[NameMapping]) -> "ApplicableCNF":
        return self

    def max_var(self) -> int:
        return 0


@dataclass(frozen=True)
class NodeStore(Mapping[str, "RecursionNode"]):
    base: Dict[str, "RecursionNode"] = field(default_factory=dict)

    def __getitem__(self, name: str) -> "RecursionNode":
        return self.base[name]

    def __setitem__(self, name: str, node: "RecursionNode"):
        self.base[name] = node

    def __len__(self) -> int:
        return len(self.base)

    def __iter__(self) -> Iterator[str]:
        return iter(self.base)


@dataclass
class RecursionChild:
    node_store: NodeStore
    id: int
    node_id: str
    input: NameMapping
    output: NameMapping
    constraint: Set[int]
    _cached: Optional["RecursionNode"] = None

    @property
    def node(self) -> "RecursionNode":
        if not self._cached:
            if self.node_id in self.node_store:
                self._cached = self.node_store[self.node_id]
            else:
                self._cached = RecursionNode(f"{self.node_id} {self.id}", DefaultApplicableCNF(self.input, self.output),
                                             [], fully_over_approximate=False)
        return self._cached

    def __hash__(self):
        return self.id

    def __eq__(self, other):
        return other.id == self.id

    def add_constraint(self, new_id: int, constraint: int) -> "RecursionChild":
        return RecursionChild(self.node_store, new_id, self.node_id, self.input, self.output,
                              self.constraint | {constraint}, self._cached)


class RecursionNode:
    """
    A node in the recursion graph
    """

    def __init__(self, id: str, acnf: ApplicableCNF, children: List[RecursionChild], fully_over_approximate: bool):
        """
        Constructor

        :param id: name of the function (just a unique id used for comparison and hashing)
        :param acnf: the cnf of this recursion node with inputs, outputs and non recursive deps
        :param children: recursive calls that lead to aborted recursion in this node
        :param fully_over_approximate: fully over approximate (don't compute the variability of the inputs)
        """
        self.id = id
        self.acnf = acnf
        self.children = children
        self.fully_over_approximate = fully_over_approximate

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        return other.id == self.id

    def child_nodes(self) -> Iterable["RecursionNode"]:
        return (child.node for child in self.children)

    def to_applicable(self,
                      child_to_dep: Callable[[RecursionChild, int], Union[Deps, Tuple[Deps, Clauses]]] =
                      lambda c, n: [Dep(frozenset(c.input.combined_clause()), frozenset(c.output.combined_clause()),
                                       frozenset(c.constraint))]) \
            -> ApplicableCNF:
        """ Create an applicable cnf that includes all deps from children """
        new_id = self.acnf.max_var() + 1
        all_deps = []
        all_clauses = []
        for child in self.children:
            deps_or_tuple = child_to_dep(child, new_id)
            if isinstance(deps_or_tuple, Dep):
                deps, clauses = deps_or_tuple, []
            else:
                deps, clauses = deps_or_tuple
            new_id = max(new_id, max((dep.max_var() for dep in deps), default=0),
                         max(max(clause, default=0) for clause in clauses) if clauses else 0) + 1
            all_deps.extend(deps)
            all_clauses.extend(clauses)
        acnf = self.acnf
        if all_clauses:
            acnf = self.acnf.add_clauses(all_clauses)
        return acnf.add_deps(all_deps)


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


@dataclass(frozen=True)
class EqClasses:
    partitions: Tuple[Tuple[int]]
    """ input partitions"""
    base: Dict[FrozenSet[int], FrozenSet[int]]

    @classmethod
    def create_default(cls, node: RecursionNode) -> "EqClasses":
        partition = node.acnf.input.combined_clause()
        output = node.acnf.output.combined_clause()
        return EqClasses((tuple(partition),), {frozenset(partition): frozenset(output)})

    def __eq__(self, other: "EqClasses") -> bool:
        return self.partitions == other.partitions and self.base == other.base

    def __hash__(self) -> int:
        return hash(self.partitions)


@dataclass
class RecursionProcessingResult:
    dep_policy: DepGenerationPolicy
    max_variability: Dict[RecursionNode, float] = field(default_factory=lambda: defaultdict(lambda: float("inf")))
    eq_classes: Dict[RecursionNode, EqClasses] = field(default_factory=dict)
    constraints: Dict[RecursionNode, Clauses] = field(default_factory=lambda: defaultdict(list))

    def get_eq_classes(self, node: RecursionNode) -> EqClasses:
        if node not in self.eq_classes:
            self.eq_classes[node] = EqClasses.create_default(node)
        return self.eq_classes[node]

    def to_meta_dep(self, node: RecursionNode) -> Callable[[RecursionChild], Deps]:
        """
        Creates a function that creates deps for a given child.

        Could be cached.
        """
        deps = []
        for inputs, outputs in self.get_eq_classes(node).base.items():
            if not outputs:
                continue
            tinputs = frozenset(inputs)
            if self.dep_policy == DepGenerationPolicy.FULL_VARS or self.dep_policy == DepGenerationPolicy.FULL_BITS:
                output_classes: List[FrozenSet[int]] = []
                if self.dep_policy == DepGenerationPolicy.FULL_VARS:
                    output_classes = [frozenset(abs(o) for o in out_vars if not is_constant(o))
                                      for out_vars in node.acnf.output.values()
                                      if any(abs(o) in outputs for o in out_vars if not is_constant(o))]
                else:
                    output_classes = [frozenset([output]) for output in outputs]
                for output in output_classes:
                    deps.append(Dep(tinputs, output, frozenset(), self.max_variability[node],
                                    fully_over_approximate=node.fully_over_approximate))
            else:
                deps.append(Dep(tinputs, frozenset(outputs), frozenset(), self.max_variability[node],
                                fully_over_approximate=node.fully_over_approximate))

        def create_m(node: RecursionNode, child: RecursionChild) -> IntToVariableMap:
            m: IntToVariableMap = {}
            m.update()
            m.update()
            return m

        def creator(child: RecursionChild) -> Deps:
            tds = transpose_deps(deps, node.acnf.input.create_mapping(child.input),
                                 node.acnf.output.create_mapping(child.output))
            constraint = frozenset(child.constraint)
            return [Dep(td.param, td.ret, constraint, td.max_variability, node.fully_over_approximate) for td in tds]

        return creator

    def to_dep(self, child: RecursionChild, start_id: int) -> Tuple[List[Dep], Clauses]:
        """
        Creates a dep with constraint for a given recursion child.

        :param start_id: start id for new variables for created clauses
        :return: dep and constraint clauses for the passed recursion child
        """
        node = child.node
        creator = self.to_meta_dep(node)
        deps = creator(child)
        misc_cons = self.constraints[node]
        if misc_cons:
            new_clauses = transpose_clauses(misc_cons, create_mapping(get_vars(misc_cons), start_id + 1))
            new_clauses_impl = [[-start_id] + clause for clause in new_clauses]
            return [Dep(dep.param, dep.ret, frozenset({start_id, *dep.constraint}),
                        dep.max_variability, dep.fully_over_approximate) for dep in deps], new_clauses_impl
        return deps, []

    def to_full_applicable(self, node: RecursionNode) -> ApplicableCNF:
        """ Maps the recursion node to a full applicable CNF with all clauses and deps for every child """
        return node.to_applicable(self.to_dep)

    def update(self, node: RecursionNode, max_variability: float = None, eq_classes: EqClasses = None) -> bool:
        changed = False
        if max_variability is not None:
            cur = self.max_variability[node]
            self.max_variability[node] = max_variability
            changed |= cur != max_variability
        if eq_classes is not None:
            cur = self.get_eq_classes(node)
            assert isinstance(eq_classes.base, dict)
            self.eq_classes[node] = eq_classes
            changed |= cur != eq_classes
        return changed


class RecursionProcessor(ABC):

    @abstractmethod
    def run(self) -> RecursionProcessingResult:
        pass


class MaxVariabilityRecursionProcessor(RecursionProcessor):
    """ Estimates the maximum variability used in dependencies """

    def __init__(self, start_nodes: List[RecursionNode],
                 variability_estimator: VariabilityEstimator,
                 state: RecursionProcessingResult):
        self.start_nodes = start_nodes
        self.variability_estimator = variability_estimator
        self.state: RecursionProcessingResult = state

    def run(self) -> RecursionProcessingResult:
        walk_recursion_nodes(self.start_nodes, RecursionNode.child_nodes, self._process)
        return self.state

    def _process(self, node: RecursionNode) -> bool:
        return self.state.update(node, max_variability=self._calculate_max_variability(node))

    def _calculate_max_variability(self, node: RecursionNode) -> float:
        if node.fully_over_approximate:
            return float("inf")
        return self.state.to_full_applicable(node).count_sat(self.variability_estimator)


class DepEqClassesRecursionProcessor(RecursionProcessor):
    """
    Estimates the input equivalence classes used for the different DepGenerationPolicies
    """

    def __init__(self, start_nodes: List[RecursionNode],
                 state: RecursionProcessingResult):
        self.start_nodes = start_nodes
        self.state: RecursionProcessingResult = state
        self.incs: Dict[RecursionNode, IncrementalRelations] = {}
        self.nvs: Dict[RecursionNode, int] = {}

    def run(self) -> RecursionProcessingResult:
        walk_recursion_nodes(self.start_nodes, RecursionNode.child_nodes, self._process)
        return self.state

    def _process(self, node: RecursionNode) -> bool:
        return self.state.update(node, eq_classes=self._compute_eq_classes(node))

    def _compute_eq_classes(self, node: RecursionNode) -> EqClasses:
        inc, nv = self._get_inc(node)
        start_id = nv + 1
        deps = []
        for child in node.children:
            deps_, clauses = self.state.to_dep(child, start_id)
            start_id = max((dep.max_var() for dep in deps_), default=1) + 1
            deps.extend(deps_)
        rels, eqs = inc.compute(deps)
        return EqClasses(tuple(map(tuple, eqs)), {frozenset(eq): rels[eq[0]] for eq in eqs})

    def _get_inc(self, node: RecursionNode) -> IncrementalRelations:
        if node not in self.incs:
            cnf = node.acnf.to_cnf()
            start: List[int] = []
            end: List[int] = []
            misc_eqs: List[List[int]] = []
            pol = self.state.dep_policy
            start = node.acnf.input.combined_clause()
            end = node.acnf.output.combined_clause()
            if pol.on_var_basis():
                misc_eqs.extend(list(node.acnf.input.values()))
                misc_eqs.extend(list(node.acnf.output.values()))
            self.incs[node] = IncrementalRelations.create(cnf, start, end, misc_eqs)
            self.nvs[node] = cnf.nv
        return self.incs[node], self.nvs[node]


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
