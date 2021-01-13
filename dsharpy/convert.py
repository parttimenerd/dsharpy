"""
Convert the --dimacs output of the modified CBMC
"""
from collections import deque
from dataclasses import dataclass, field
from io import IOBase
from typing import List, Set, Callable, Iterable, Optional, TypeVar, Dict, Tuple, Deque

import click

from dsharpy.formula import DCNF
from dsharpy.util import VariableSet


@dataclass
class Node:

    sat_var: Optional[int]
    neighbors: List["Node"]
    var: Optional["VarNode"] = field(default_factory=lambda: None)

    def __str__(self):
        return str(self.sat_var)

    def __repr__(self):
        return f"Node({self.sat_var})"

    def __hash__(self):
        return self.sat_var or id(self)


T = TypeVar("T")


def bfs(start: Iterable[T], visit: Callable[[T], Optional[Iterable[T]]]):
    visited: Set[T] = set()
    deq: Deque[T] = deque()
    deq.extend(start)
    while len(deq) > 0:
        top = deq.pop()
        if top in visited:
            continue
        visited.add(top)
        top_v = visit(top)
        if top_v:
            deq.extendleft(top_v)


class VarNode:

    def __init__(self, name: str, sat_vars: List[Node], raw_sat: List[str]):
        self.name = name
        self.sat_vars = sat_vars
        self.var_deps = set()  # type: Set[VarNode]
        self.raw_sat = raw_sat

    def clear_var_deps(self):
        self.var_deps.clear()

    def add_var_deps(self):
        def visit(node: Node):
            if isinstance(node, VarNode):
                self.var_deps.add(node)
            elif node.var and node.var != self:
                self.var_deps.add(node.var)
            else:
                return node.neighbors

        bfs(self.sat_vars, visit)
        for dep in self.var_deps:
            dep.var_deps.add(self)

    def compute_others(self, vars: List["VarNode"], without_crossing: List["VarNode"]) -> Set["VarNode"]:
        ret: Set["VarNode"] = set()

        def visit(node: VarNode):
            if node in without_crossing:
                return
            elif node in vars:
                ret.add(node)
            else:
                return node.var_deps

        bfs(self.var_deps, visit)
        return ret

    def __str__(self):
        return self.name

    def __repr__(self):
        return f"VarNode({self})"


def var_nodes_to_ints(var_nodes: Iterable[VarNode]) -> Iterable[int]:
    return list(v.sat_var for o in var_nodes for v in o.sat_vars)


@dataclass(frozen=True)
class ParentId:
    loop: bool
    id: int


@dataclass
class Aborted:

    parent: Optional[ParentId]
    representative: "Aborted"

    def self_representative(self) -> bool:
        return self.representative == self


@dataclass(eq=True)
class LoopIter(Aborted):

    id: int
    func_id: str
    nr: int

    input: List[VarNode]

    last_iter_guard: Optional[VarNode]
    last_iter_input: List[VarNode]
    last_iter_output: List[VarNode]

    output: List[VarNode]

    def __post_init__(self):
        if isinstance(self.last_iter_guard, list):
            self.last_iter_guard = self.last_iter_guard[0] if self.last_iter_guard else None

    def input_that_outputs_might_depend_on(self) -> Set[VarNode]:
        meta_node = VarNode("meta", [v for o in self.last_iter_output for v in o.sat_vars], [])
        meta_node.var_deps.update(set(v for o in self.last_iter_output for v in o.var_deps))
        return meta_node.compute_others(self.input, self.last_iter_output)

    def compute_dependencies(self) -> Tuple[Iterable[int], Iterable[int]]:
        """ requires that set_var_deps has been called on all VarNodes before """
        return var_nodes_to_ints(self.input_that_outputs_might_depend_on()), var_nodes_to_ints(self.output)

    def compute_dependency_strings(self) -> str:
        """ requires that set_var_deps has been called on all VarNodes before """
        return DCNF.format_dep_comment(*self.compute_dependencies())

    def __hash__(self):
        return hash([self.id, self.func_id, self.nr])


@dataclass(eq=True)
class AbortedRecursion(Aborted):
    id: str
    returns: List[VarNode]
    params: List[VarNode]

    def compute_dependencies(self) -> Tuple[Iterable[int], Iterable[int]]:
        return var_nodes_to_ints(self.params), var_nodes_to_ints(self.returns)

    def compute_dependency_strings(self) -> str:
        return DCNF.format_dep_comment(*self.compute_dependencies())

    def __hash__(self):
        return hash(self.id)


class Graph:

    def __init__(self):
        self.var_nodes: Dict[str, VarNode] = {}
        self.sat_nodes: List[Node] = []
        self.loop_iters: List[LoopIter] = []
        self.loop_representative: Dict[(str, int), LoopIter] = {}  # (func_id, loop_nr) → last loop iter
        self.recursions: List[AbortedRecursion] = []
        self.recursion_representative: Dict[str, AbortedRecursion] = {}
        self.relations: List[List[VarNode]] = []

    def get_sat_node(self, var: int) -> Node:
        var = abs(var)
        while len(self.sat_nodes) <= var:
            self.sat_nodes.append(Node(len(self.sat_nodes), []))
        return self.sat_nodes[var]

    def get_var_node(self, var: str) -> VarNode:
        if var not in self.var_nodes:
            self.var_nodes[var] = VarNode(var, [], [])
        return self.var_nodes[var]

    def update_var_deps(self):
        for var_node in self.var_nodes.values():
            var_node.clear_var_deps()
        for var_node in self.var_nodes.values():
            var_node.add_var_deps()
        for i, relation in enumerate(self.relations):
            var = VarNode(f"relation_{i}", [], [])
            var.var_deps = relation
            for node in relation:
                node.var_deps.add(var)

    def _parse_variables(self, var_str: str) -> List[VarNode]:
        return [self.get_var_node(var) for var in var_str.split(" ") if len(var) > 0]

    @staticmethod
    def is_loop_line(line: str) -> bool:
        return line.startswith("c loop ")

    @staticmethod
    def is_recursion_line(line: str) -> bool:
        return line.startswith("c recursion ") and " | parent " in line

    @staticmethod
    def is_sat_line(line: str) -> bool:
        return line.endswith(" 0") and (
                    line.split(" ", maxsplit=1)[0].isdigit() or (line.startswith("-") and line[1].isdigit()))

    @staticmethod
    def is_var_line(line: str) -> bool:
        return line.startswith("c ") and (
                    line.split(" ")[-1].split("-")[-1].isdigit() or line.endswith("FALSE") or line.endswith("TRUE"))

    @staticmethod
    def is_relate_line(line: str) -> bool:
        return line.startswith("c relate ")

    def _parse_parent(self, parent_part: str) -> Optional[ParentId]:
        parent = parent_part.strip()[len("parent "):]
        if parent == "none":
            return None
        else:
            num = int(parent.split(" ")[1])
            return ParentId(parent.startswith("loop"), num)

    def _parse_variables(self, vars: str, remove_first: bool) -> List[VarNode]:
        parts = vars.split(" ")[1 if remove_first else 0:]
        return [self.get_var_node(var) for var in parts]

    def _parse_loop_line(self, line: str):
        """
        parse lines like "c loop 0 main 0 | parent none | input main::1::num!0@1#2 | lguard goto_symex::\\guard#3 | linput | loutput | output"
        """
        id_part, parent_part, input_part, lguard_part, linput_part, loutput_part, output_part = line[len("c loop "):].split(" | ")
        id_str, func_str, nr_str = id_part.split(" ")
        iter = LoopIter(self._parse_parent(parent_part), None, int(id_str), func_str, int(nr_str),
                        *(self._parse_variables(part, remove_first=True) for part in (input_part, lguard_part, linput_part, loutput_part, output_part)))
        self.loop_iters.append(iter)
        if (iter.func_id, iter.nr) not in self.loop_representative:
            self.loop_representative[(iter.func_id, iter.nr)] = iter
            iter.representative = iter
        else:
            iter.representative = self.loop_representative[(iter.func_id, iter.nr)]

    def _parse_recursion_line(self, line: str):
        id_part, parent_part, return_part, param_part = line[len("c recursion "):].split(" | ")
        rec = AbortedRecursion(self._parse_parent(parent_part), id_part, None,
                               self._parse_variables(return_part, remove_first=True),
                               self._parse_variables(param_part, remove_first=True))
        self.recursions.append(rec)
        if rec.id not in self.recursion_representative:
            self.recursion_representative[rec.id] = rec
            rec.representative = rec
        else:
            rec.representative = self.recursion_representative[rec.id]
        inner_node = Node(None, [])
        for v in rec.returns + rec.params:
            for s in v.sat_vars:
                inner_node.neighbors.append(s)
                s.neighbors.append(s)

    def _parse_sat_line(self, line: str):
        vars = [self.get_sat_node(int(i)) for i in line.split(" ")[:-1]]
        new_node = Node(None, vars)
        for var in vars:
            var.neighbors.append(new_node)

    def _parse_var_line(self, line: str):
        c, var, *sat_vars = line.split(" ")
        sat_nodes = [self.get_sat_node(int(s)) for s in sat_vars if s.isdigit() or (s[1:].isdigit() and s[0] == "-")]
        var_node = self.get_var_node(var)
        var_node.sat_vars.extend(sat_nodes)
        var_node.raw_sat.extend(list(sat_vars))
        for sat_node in sat_nodes:
            sat_node.var = var_node

    @staticmethod
    def is_oa_if_line(line: str) -> bool:
        return line.startswith("c oa if ")

    def _parse_oa_if_line(self, line: str):
        c, oa, _if, orig_cond, cond = line.split(" ")
        orig_sat = self.get_sat_node(int(orig_cond))
        sat = self.get_sat_node(int(cond))
        orig_sat.neighbors.append(sat)
        sat.neighbors.append(orig_sat)

    def parse_relate_line(self, line: str):
        self.relations.append([self.get_var_node(part) for part in line.split(" ")[2:]])

    def find_ind_vars(self, ind_var_prefix: str) -> Iterable[int]:
        variables = [var_node for var_node in self.var_nodes.values() if
                     ("::" + ind_var_prefix + "!") in var_node.name and var_node.name.endswith("#2")]
        return var_nodes_to_ints(variables)

    @classmethod
    def process(cls, infile: IOBase, out: IOBase, ind_var_prefix: str = None):
        graph = Graph()
        lines = []
        for line in infile.readlines():
            line = line.strip()
            if Graph.is_loop_line(line):
                graph._parse_loop_line(line)
            elif Graph.is_sat_line(line):
                graph._parse_sat_line(line)
                lines.append(line)
            elif Graph.is_var_line(line):
                graph._parse_var_line(line)
                lines.append(line)
            elif Graph.is_oa_if_line(line):
                graph._parse_oa_if_line(line)
            elif Graph.is_recursion_line(line):
                graph._parse_recursion_line(line)
            elif Graph.is_relate_line(line):
                graph.parse_relate_line(line)
            elif line.startswith("c ") or line.startswith("p "):
                lines.append(line)
        graph.update_var_deps()
        if ind_var_prefix:
            ind = graph.find_ind_vars(ind_var_prefix)
            lines.append(DCNF.format_ind_comment(ind))
        for loop_iter in graph.loop_iters + graph.recursions:
            lines.append(loop_iter.compute_dependency_strings())
        out.writelines(line + "\n" for line in lines)


@click.command(name="convert", help="""
Convert output of modified CBMC to D#SAT formulas.

Variables that start with __out are used for creating "c ind" statements (only their first assignment).
""")
@click.argument('infile', type=click.File(mode="r"), required=False, default="-")
@click.argument('outfile', type=click.File(mode="w"), required=False, default="-")
def cli(infile: IOBase, outfile: IOBase):
    Graph.process(infile, outfile, ind_var_prefix="__out")


if __name__ == '__main__':
    cli()
