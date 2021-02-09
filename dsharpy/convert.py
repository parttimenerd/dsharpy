"""
Convert the --dimacs output of the modified CBMC
"""
from dataclasses import dataclass, field
from io import IOBase
from typing import List, Set, Iterable, Optional, TypeVar, Dict, Tuple, Union, FrozenSet

import click

from dsharpy.formula import DCNF, Dep
from dsharpy.recursion_graph import NameMapping, RecursionNode, RecursionProcessingResult, \
    MaxVariabilityRecursionProcessor, \
    RecursionChild, ApplicableCNF, Clause, parse_variable, NodeStore, DepEqClassesRecursionProcessor
from dsharpy.util import bfs, DepGenerationPolicy

Origin = Union[Dep, RecursionChild, int]


@dataclass
class Node:
    sat_var: Optional[int]
    neighbors: List["Node"]
    var: Optional["VarNode"] = field(default_factory=lambda: None)
    origin: List[Origin] = field(default_factory=list)
    """ Either an aborted recursion, a dependency or a clause (index into cnf.clauses) """

    def __str__(self):
        return str(self.sat_var)

    def __repr__(self):
        return f"Node({self.sat_var})"

    def __hash__(self):
        return self.sat_var or id(self)


T = TypeVar("T")


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
    return list(v.sat_var for o in var_nodes for v in o.sat_vars if v.sat_var)


def var_nodes_to_abs_set(var_nodes: Iterable[VarNode]) -> FrozenSet[int]:
    return frozenset(abs(v.sat_var) for o in var_nodes for v in o.sat_vars if v.sat_var)


@dataclass
class Aborted:
    representative: "Aborted"

    guards: List[Tuple[VarNode, bool]]

    def self_representative(self) -> bool:
        return self.representative == self

    def guard_conjunction(self) -> FrozenSet[int]:
        return frozenset(
            sat_var.sat_var * (1 if is_true else -1) for guard, is_true in self.guards for sat_var in guard.sat_vars
            if sat_var.sat_var)


@dataclass(eq=True)
class LoopIter(Aborted):
    """ Represents the loopt class from CBMC """

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

    def input_that_outputs_might_depend_on(self, output: List[VarNode] = None) -> Set[VarNode]:
        output = output or self.last_iter_output
        meta_node = VarNode("meta", [v for o in output for v in o.sat_vars], [])
        meta_node.var_deps.update(set(v for o in output for v in o.var_deps))
        return meta_node.compute_others(self.input, output)

    def compute_dependencies(self, dep_policy: DepGenerationPolicy) -> List[Dep]:
        """
        requires that set_var_deps has been called on all VarNodes before

        todo: does not support all DepGenerationPolicies
        """
        guard = self.guard_conjunction()
        if dep_policy == DepGenerationPolicy.SINGLE_DEP:
            return [Dep(frozenset(var_nodes_to_ints(self.input_that_outputs_might_depend_on())),
                        frozenset(var_nodes_to_ints(self.output)), guard)]
        else:
            # find equivalence classes

            if dep_policy == DepGenerationPolicy.SINGLE_DEP:
                outss = []
                inss = []
                for out in self.last_iter_output:
                    ins = frozenset(self.input_that_outputs_might_depend_on([out]))
                    if ins:
                        inss.extend(ins)
                        outss.append(out)
                return [Dep(var_nodes_to_abs_set(inss), var_nodes_to_abs_set(outss), guard)]

            if dep_policy.on_var_basis():
                eqs: Dict[FrozenSet[VarNode], List[VarNode]] = {}
                for out in self.last_iter_output:
                    ins = frozenset(self.input_that_outputs_might_depend_on([out]))
                    if ins not in eqs:
                        eqs[ins] = []
                    eqs[ins].append(out)

                if dep_policy == DepGenerationPolicy.FULL_VARS:
                    return [Dep(var_nodes_to_abs_set(ins), var_nodes_to_abs_set([out]), guard) for ins, outs in
                            eqs.items() for out in outs]
                elif dep_policy == DepGenerationPolicy.MULTIPLE_DEP_VARS:
                    return [Dep(var_nodes_to_abs_set(ins), var_nodes_to_abs_set(outs), guard) for ins, outs in
                            eqs.items()]
                assert False
            else:
                assert False
            assert False

    def __hash__(self):
        return hash([self.id, self.func_id, self.nr])


class Graph:

    def __init__(self):
        self.cnf = DCNF()
        self.var_nodes: Dict[str, VarNode] = {}
        self.sat_nodes: List[Node] = []
        self.loop_iters: List[LoopIter] = []
        self.loop_representative: Dict[(str, int), LoopIter] = {}  # (func_id, loop_nr) → last loop iter
        self.relations: List[List[VarNode]] = []
        self.rec_nodes: NodeStore = NodeStore()
        self._finished_rec_nodes = False
        self.rec_children: List[RecursionChild] = []

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

    def _parse_variables(self, vars: str, remove_first: bool) -> List[VarNode]:
        parts = vars.split(" ")[1 if remove_first else 0:]
        return [self.get_var_node(var) for var in parts]

    def _parse_loop_line(self, line: str):
        """
        parse lines like "c loop 0 main 0 | input main::1::num!0@1#2 | guards goto_symex::\\guard#3 | lguard goto_symex::\\guard#3 | linput | loutput | output"
        """
        id_part, input_part, guards_part, lguard_part, linput_part, loutput_part, output_part = line[len(
            "c loop "):].split(" | ")
        id_str, func_str, nr_str = id_part.split(" ")
        iter = LoopIter(None, self._parse_guards(guards_part[len("guards "):]),
                        int(id_str), func_str, int(nr_str),
                        *(self._parse_variables(part, remove_first=True) for part in
                          (input_part, lguard_part, linput_part, loutput_part, output_part)))
        self.loop_iters.append(iter)
        if (iter.func_id, iter.nr) not in self.loop_representative:
            self.loop_representative[(iter.func_id, iter.nr)] = iter
            iter.representative = iter
        else:
            iter.representative = self.loop_representative[(iter.func_id, iter.nr)]

    def _parse_guards(self, guard_part: str) -> List[Tuple[VarNode, bool]]:
        ret = []
        for var in guard_part.split(" "):
            if not var:
                continue
            neg = var[0] == "-"
            ret.append((self.get_var_node(var[int(neg):]), not neg))
        return ret

    def _parse_sat_line(self, line: str):
        clause = [int(i) for i in line.split(" ")[:-1]]
        self.cnf.append(clause)
        vars = [self.get_sat_node(i) for i in clause]
        new_node = Node(None, vars)
        new_node.origin.append(len(self.cnf.clauses) - 1)
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

    def _parse_relate_line(self, line: str):
        self.relations.append([self.get_var_node(part) for part in line.split(" ")[2:]])

    def find_ind_vars(self, ind_var_prefix: str, use_latest_ind_var: bool = True) -> Iterable[int]:
        variables: Dict[str, int] = {}
        for var in [var_node.name for var_node in self.var_nodes.values() if
                     ("::" + ind_var_prefix) in var_node.name or ("." + ind_var_prefix) in var_node.name]:
            base, num = var.split("#")
            if base not in variables:
                variables[base] = num
            else:
                variables[base] = max(variables[base], num)

        return var_nodes_to_ints([self.get_var_node(f"{var}#{num}") for var, num in variables.items()])

    def _add_dep(self, dep: Dep):
        self.cnf.add_dep(dep)
        rel = []
        for vs in [dep.param, dep.ret, dep.constraint]:
            for v in vs:
                var_node = self.get_sat_node(v)
                var_node.origin.append(dep)
                rel.append(var_node)
        self._relate(rel)

    def _parse_dep(self, line: str):
        dep = Dep.from_comment(line)
        self._add_dep(dep)

    @staticmethod
    def is_recursion_child_line(line: str) -> bool:
        return line.startswith("c rec child ")

    def _parse_mapping(self, part: str, tag: str) -> NameMapping:
        """
        Parses "TAG VAR_1 ACTUAL_VAR_1 … VAR_N ACTUAL_VAR_N" into a name mapping

        Only valid if all variable lines are parsed
        """
        assert part.startswith(tag)
        mapping: Dict[str, Clause] = {}
        parts = part[len(tag) + 1:].split(" ")
        if not parts[0] and len(parts) == 1:
            return NameMapping()
        assert len(parts) % 2 == 0
        for i in range(0, len(parts), 2):
            variables = [parse_variable(v) for v in self.get_var_node(parts[i + 1]).raw_sat]
            assert variables
            mapping[parts[i]] = variables
        return NameMapping(mapping)

    def _parse_rec_child_line(self, line: str):
        """ Only valid if all variable lines are parsed """
        id_and_func_part, input_part, output_part, constraint_part = line[len("c rec child "):].split(" | ")
        id_part, func_name = id_and_func_part.strip().split(" ")
        rec_child = RecursionChild(self.rec_nodes, int(id_part), func_name,
                                   self._parse_mapping(input_part, "input"),
                                   self._parse_mapping(output_part, "output"),
                                   {int(v.sat_var) for var in constraint_part.split(" ") if var != "0"
                                    for v in self.get_var_node(var).sat_vars if v.sat_var})
        self.rec_children.append(rec_child)
        rel = []
        for vs in [rec_child.input.combined_clause(), rec_child.output.combined_clause(), rec_child.constraint]:
            for v in vs:
                var_node = self.get_sat_node(v)
                var_node.origin.append(rec_child)
                rel.append(var_node)
        self._relate(rel)

    @staticmethod
    def _relate(sat_nodes: List[Node]):
        var = Node(None, sat_nodes)
        for sat_node in sat_nodes:
            sat_node.neighbors.append(var)

    @staticmethod
    def is_recursion_node_line(line: str) -> bool:
        return line.startswith("c rec node ")

    def _parse_recursion_node_line(self, line: str):
        """ Only valid if all variable lines are parsed """
        func_id_part, input_part, output_part = line[len("c rec node "):].split(" | ")
        func_id = func_id_part.strip()

        inputs = self._parse_mapping(input_part, "input")
        outputs = self._parse_mapping(output_part, "output")

        self.rec_nodes[func_id] = RecursionNode(func_id, ApplicableCNF(inputs, outputs, [], []), [])

    @staticmethod
    def _find_origins(start_nodes: List[Node]) -> Set[Origin]:
        """
        Find all nodes that the start nodes are related to (and themselves) and return their combined
        origins
        """
        origins: Set[Origin] = set()

        def visit(node: Node):
            origins.update(node.origin)
            return node.neighbors

        bfs(start_nodes, visit)
        return origins

    def _create_recursion_graph(self) -> List[RecursionNode]:
        """
        Creates the proper recursion nodes and remove the deps and children from the graph that belong
        to a recursion node
        """
        if self._finished_rec_nodes or not self.rec_nodes:
            return list(self.rec_nodes.values())
        rec_children: Set[RecursionChild] = set(self.rec_children)
        deps: Set[Dep] = set(self.cnf.deps)
        clauses: Set[int] = set(range(len(self.cnf.clauses)))

        for node in self.rec_nodes.values():
            # given a recursion node, find
            #   - the clauses and deps that belong to it
            #   - find its children

            node_deps: Set[Dep] = set()
            node_children: Set[RecursionChild] = set()
            node_clauses: Set[int] = set()

            # vars that are related to the return
            return_vars = [self.get_sat_node(var) for var in node.acnf.output.combined_clause()]

            for origin in self._find_origins(return_vars):
                if isinstance(origin, Dep):
                    node_deps.add(origin)
                    deps.remove(origin)
                elif isinstance(origin, RecursionChild):
                    node_children.add(origin)
                    rec_children.remove(origin)
                else:
                    assert isinstance(origin, int)
                    node_clauses.add(origin)
                    clauses.remove(origin)

            node.children = list(node_children)
            node.acnf.deps = list(node_deps)
            node.acnf.clauses = [self.cnf.clauses[i] for i in node_clauses]

        self.rec_children = list(rec_children)
        self.cnf.set_deps(list(deps))
        self.cnf.clauses = [self.cnf.clauses[i] for i in clauses]
        self._finished_rec_nodes = True
        return list(self.rec_nodes.values())

    def process_recursion_graph(self, dep_policy: DepGenerationPolicy) -> RecursionProcessingResult:
        # todo: currently only uses the default config for variability over approximation
        from dsharpy.counter import State
        rec = self._create_recursion_graph()
        state = RecursionProcessingResult(dep_policy)
        DepEqClassesRecursionProcessor(rec, state).run()
        MaxVariabilityRecursionProcessor(rec, lambda c: State(c).compute(), state).run()
        return state

    @classmethod
    def parse_graph(cls, raw_lines: List[str], dep_policy: DepGenerationPolicy, ind_var_prefix: str = None,
                    use_latest_ind_var: bool = True) -> "Graph":
        graph = Graph()
        lines = []
        recursion_child_lines: List[str] = []
        recursion_node_lines: List[str] = []
        for line in raw_lines:
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
            elif Graph.is_relate_line(line):
                graph._parse_relate_line(line)
            elif Graph.is_recursion_child_line(line):
                recursion_child_lines.append(line)
            elif Graph.is_recursion_node_line(line):
                recursion_node_lines.append(line)
            elif line.startswith("c dep "):
                graph._parse_dep(line)
            elif line.startswith("c ") or line.startswith("p "):
                lines.append(line)
                graph.cnf.comments.append(line)
        for recursion_child_line in recursion_child_lines:
            graph._parse_rec_child_line(recursion_child_line)
        for recursion_node_line in recursion_node_lines:
            graph._parse_recursion_node_line(recursion_node_line)
        graph.update_var_deps()
        if ind_var_prefix:
            ind = graph.find_ind_vars(ind_var_prefix, use_latest_ind_var)
            graph.cnf.add_ind(*ind)
        for loop_iter in graph.loop_iters:
            for dep in loop_iter.compute_dependencies(dep_policy):
                graph._add_dep(dep)

        proc_res = graph.process_recursion_graph(dep_policy)
        for rec_child in graph.rec_children:
            deps, clauses = proc_res.to_dep(rec_child, graph.cnf.nv + 1)
            for dep in deps:
                graph.cnf.add_dep(dep)
            graph.cnf.append(clauses)

        return graph

    @classmethod
    def process(cls, infile: IOBase, out: IOBase, dep_policy: DepGenerationPolicy, ind_var_prefix: str = None,
                use_latest_ind_var: bool = True):
        cls.parse_graph(infile.readlines(), dep_policy, ind_var_prefix, use_latest_ind_var).cnf.to_fp(out)


@click.command(name="convert", help="""
Convert output of modified CBMC to D#SAT formulas.

Variables that start with __out are used for creating "c ind" statements (only their first assignment).
""")
@click.argument('infile', type=click.File(mode="r"), required=False, default="-")
@click.argument('outfile', type=click.File(mode="w"), required=False, default="-")
@click.argument('dep_gen_policy', type=DepGenerationPolicy, default=DepGenerationPolicy.FULL_VARS)
def cli(infile: IOBase, outfile: IOBase, dep_gen_policy: DepGenerationPolicy):
    Graph.process(infile, outfile, dep_gen_policy, ind_var_prefix="__out")


if __name__ == '__main__':
    cli()
