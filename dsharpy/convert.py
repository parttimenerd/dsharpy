"""
Convert the --dimacs output of the modified CBMC
"""
import itertools
from collections import deque
from dataclasses import dataclass, field
from io import IOBase
from pathlib import Path
from typing import List, Set, Callable, Iterable, Optional, TypeVar, Dict, Tuple, Deque

import click

from dsharpy.formula import DCNF


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

    def set_var_deps(self):
        self.var_deps.clear()

        def visit(node: Node):
            if isinstance(node, VarNode):
                self.var_deps.add(node)
            elif node.var and node.var != self:
                self.var_deps.add(node.var)
            else:
                return node.neighbors
        bfs(self.sat_vars, visit)

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


@dataclass
class LoopIter:

    inner: List[VarNode]
    outer: List[VarNode]

    def compute_dependencies(self) -> Tuple[Iterable[int], Iterable[int]]:
        """ requires that set_var_deps has been called on all VarNodes before """
        meta_node = VarNode("meta", [v for o in self.outer for v in o.sat_vars], [])
        return set(var_nodes_to_ints(self.outer)), var_nodes_to_ints(meta_node.compute_others(self.inner, self.outer))

    def compute_dependency_strings(self) -> str:
        """ requires that set_var_deps has been called on all VarNodes before """
        return DCNF.format_dep_comment(*self.compute_dependencies())


@dataclass
class AbortedRecursion:

    returns: List[VarNode]
    params: List[VarNode]

    def compute_dependencies(self) -> Tuple[Iterable[int], Iterable[int]]:
        return var_nodes_to_ints(self.params), var_nodes_to_ints(self.returns)

    def compute_dependency_strings(self) -> str:
        return DCNF.format_dep_comment(*self.compute_dependencies())


class Graph:

    def __init__(self):
        self.var_nodes: Dict[str, VarNode] = {}
        self.sat_nodes: List[Node] = []
        self.loop_iters: List[LoopIter] = []
        self.recursions: List[AbortedRecursion] = []


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
            var_node.set_var_deps()

    def _parse_variables(self, var_str: str) -> List[VarNode]:
        return [self.get_var_node(var) for var in var_str.split(" ") if len(var) > 0]

    @staticmethod
    def is_loop_line(line: str) -> bool:
        return line.startswith("c loop ")

    @staticmethod
    def is_recursion_line(line: str) -> bool:
        return line.startswith("c recursion return ")

    @staticmethod
    def is_sat_line(line: str) -> bool:
        return line.endswith(" 0") and (line.split(" ", maxsplit=1)[0].isdigit() or (line.startswith("-") and line[1].isdigit()))

    @staticmethod
    def is_var_line(line: str) -> bool:
        return line.startswith("c ") and (line.split(" ")[-1].split("-")[-1].isdigit() or line.endswith("FALSE") or line.endswith("TRUE"))

    def _parse_loop_line(self, line: str):
        inner, outer = line.split("| outer")
        inner = inner.split("assigned ", maxsplit=1)[1]
        self.loop_iters.append(LoopIter(self._parse_variables(inner), self._parse_variables(outer)))

    def _parse_recursion_line(self, line: str):
        return_var, params = line.split("| param")
        return_var = return_var[len("c recursion return "):]
        rec = AbortedRecursion(self._parse_variables(return_var), self._parse_variables(params))
        self.recursions.append(rec)
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

    def find_ind_vars(self, ind_var_prefix: str) -> Iterable[int]:
        variables = [var_node for var_node in self.var_nodes.values() if ("::" + ind_var_prefix + "!") in var_node.name and var_node.name.endswith("#2")]
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
