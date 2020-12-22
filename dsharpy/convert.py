"""
Convert the --dimacs output of the modified CBMC
"""
import itertools
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Set, Callable, Iterable, Optional, TypeVar, Dict, Tuple

import click


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
    deq = deque()
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

@dataclass
class LoopIter:

    inner: List[VarNode]
    outer: List[VarNode]

    def compute_dependencies(self) -> List[Tuple[int, List[int]]]:
        """ requires that set_var_deps has been called on all VarNodes before """
        ret = []
        for o in self.outer:
            inner = o.compute_others(self.inner, self.outer)
            print(f"{o} -> {inner}")
            inner_sat = [s.sat_var for i in inner for s in i.sat_vars]
            for s in o.sat_vars:
                ret.append((s, inner_sat))
        return ret

    def compute_dependency_strings(self) -> List[str]:
        """ requires that set_var_deps has been called on all VarNodes before """
        return [f"c dep {a} {' '.join(map(str, bs))} 0" for a, bs in self.compute_dependencies()]


@dataclass
class AbortedRecursion:

    returns: List[VarNode]
    params: List[VarNode]

    def compute_dependencies(self) -> List[Tuple[int, List[int]]]:
        return [(p_var.sat_var, [r_var.sat_var
                                 for r in self.returns
                                 for r_var in r.sat_vars])
                for p in self.params
                for p_var in p.sat_vars]

    def compute_dependency_strings(self) -> List[str]:
        return [f"c dep {a} {' '.join(map(str, bs))} 0" for a, bs in self.compute_dependencies()]


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

    @classmethod
    def process(cls, infile: Path, outfile: Path):
        graph = Graph()
        lines = []
        with infile.open() as f:
            for line in f.readlines():
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
        for loop_iter in graph.loop_iters + graph.recursions:
            lines.extend(loop_iter.compute_dependency_strings())
        with outfile.open("w") as f:
            f.writelines(line + "\n" for line in lines)


@click.command(name="convert", help="Convert output of modified CBMC to D#SAT formulas")
@click.argument('infile', type=Path)
@click.argument('outfile', type=Path)
def cli(infile: Path, outfile: Path):
    Graph.process(infile, outfile)


if __name__ == '__main__':
    cli()
