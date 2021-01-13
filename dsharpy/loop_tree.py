"""
Build abstract versions of loops and recursion, to find basic invariants that can be used to improve the leakage
computation.
"""
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import List, Tuple, Mapping, Iterator, Dict, Set, MutableMapping, Optional

from pysat.formula import CNF

Clause = List[int]
Clauses = List[Clause]

IntMap = MutableMapping[int, int]


def get_vars(clauses: Clauses) -> Set[int]:
    return set(abs(v) for clause in clauses for v in clause)


def create_mapping(vars: Set[int], new_start: int = 0, keep: List[int] = None, custom_mapping: IntMap = None) -> IntMap:
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


def transpose_clauses(clauses: Clauses, mapping: IntMap) -> Clauses:
    return [[mapping[v] if v in mapping else 0 for v in clause] for clause in clauses]


@dataclass(frozen=True)
class NameMapping(Mapping[str, Clause]):

    base: Dict[str, Clause]

    def normalize(self) -> "NameMapping":
        return NameMapping({self.normalize_name(name): vars for name, vars in self.items()})

    @staticmethod
    def normalize_name(name: str) -> str:
        return name.split("#")[0]

    def __getitem__(self, name: str) -> Clause:
        return self.base[name]

    def __len__(self) -> int:
        return len(self.base)

    def __iter__(self) -> Iterator[str]:
        return iter(self.base)

    def transpose(self, mapping: IntMap) -> "NameMapping":
        return NameMapping({name: transpose_clauses([c], mapping)[0] for name, c in self.base.items()})

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

    def create_mapping(self, other: "NameMapping") -> IntMap:
        ret = {}
        for name in self.base:
            ret.update({i1: i2 for i1, i2 in zip(self.base[name], other.base[name])})
        return ret

@dataclass
class ApplicableCNF:
    """
    An abstract function, declared in CNF, that can be applied
    """

    input: NameMapping
    """ positive integers, 0 means that a SAT variable can safely be ignored """
    output: NameMapping
    clauses: Clauses
    misc_vars: NameMapping = field(default_factory=lambda: NameMapping({}))

    def transpose(self, new_start: int, keep: List[int] = None, custom_mapping: IntMap = None) -> "ApplicableCNF":
        mapping = create_mapping(get_vars(self.clauses), new_start, keep, custom_mapping)
        return ApplicableCNF(self.input.transpose(mapping), self.output.transpose(mapping),
                             transpose_clauses(self.clauses, mapping), self.misc_vars.transpose(mapping))

    def apply(self, new_start: int, input: NameMapping, output: Optional[NameMapping]) -> "ApplicableCNF":
        """
        Applies the CNF to the passed input mapping, after transposing the formula
        :param output: an empty name mapping is equivalent to: create new variables
        :return: applied formula
        """
        if not self.input.check(input) or (output and not self.output.check(output)):
            raise AssertionError("Mappings are invalid")
        mapping = self.input.create_mapping(input)
        if output:
            mapping.update(self.output.create_mapping(output))
        return self.transpose(new_start, custom_mapping=mapping)


class Node(ABC):
    """
    A node in the loop and recursion tree
    """

    def __init__(self, input: NameMapping, output: NameMapping, children: List["Node"]):
        self.input = input
        self.output = output
        self.children = children

    @abstractmethod
    def iterate(self, new_start: int) -> "Node":
        """ keeps in- and output the same, new_start is only used for additions """
        pass

    @abstractmethod
    def clauses(self) -> Clauses:
        """ Return the clauses that represent this node """
        pass

    def cnf(self) -> CNF:
        return CNF(from_clauses=self.clauses())


class LoopNode(Node):
    """
    A loop is mapping of loop defined variables (inputs and outputs have to be the same) with a body
    that contains the guard variable in its misc variables
    """

    def __init__(self, input: NameMapping, output: NameMapping, children: List["Node"], body: ApplicableCNF,
                 guard: str):
        super().__init__(input, output, children)
        assert input.keys() == output.keys()
        self.body = body
        self.guard = guard
        assert self.guard in self.body.misc_vars

    def iterate(self, new_start: int) -> "LoopNode":
        pass

    def clauses(self) -> Clauses:
        pass


class SimpleInvariantFinder:
    """ Finds invariants """


    def process(self, node: Node) -> ApplicableCNF:
        pass

