"""
Convert the --dimacs output of the modified CBMC
"""
from collections import defaultdict
from dataclasses import dataclass, field
from io import IOBase
from typing import List, Set, Iterable, Optional, TypeVar, Dict, Tuple, Union, FrozenSet, Mapping

import click

from dsharpy.formula import DCNF, Dep
from dsharpy.recursion_graph import NameMapping, RecursionNode, RecursionProcessingResult, \
    MaxVariabilityRecursionProcessor, \
    RecursionChild, ApplicableCNF, Clause, parse_variable, NodeStore, DepEqClassesRecursionProcessor, Variables
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
    fully_over_approximate: bool
    parent_loop: Optional[int]

    # related to the last iteration
    guard: Optional[VarNode]
    input: Tuple[List[VarNode], NameMapping]
    inner_input: Tuple[List[VarNode], NameMapping]
    misc_input: Tuple[List[VarNode], NameMapping]
    inner_output: Tuple[List[VarNode], NameMapping]
    output: Tuple[List[VarNode], NameMapping]

    def __hash__(self):
        return hash([self.id, self.func_id, self.nr])


@dataclass
class Consumed:
    """ Used for preprocessing loops """
    consumed_children: Set[RecursionChild] = field(default_factory=set)
    consumed_nodes: Set[RecursionNode] = field(default_factory=set)
    consumed_deps: Set[Dep] = field(default_factory=set)
    consumed_clauses: Set[int] = field(default_factory=set)

    def __or__(self, other: "Consumed") -> "Consumed":
        return Consumed(self.consumed_children | other.consumed_children,
                        self.consumed_nodes | other.consumed_nodes,
                        self.consumed_deps | other.consumed_deps,
                        self.consumed_clauses | other.consumed_clauses)

    def update(self, other: "Consumed"):
        self.consumed_clauses.update(other.consumed_clauses)
        self.consumed_deps.update(other.consumed_deps)
        self.consumed_children.update(other.consumed_children)
        self.consumed_nodes.update(other.consumed_nodes)

    def combined(self) -> Set[Origin]:
        return self.consumed_children | self.consumed_deps | self.consumed_clauses


@dataclass
class LoopIterNode:
    iter: LoopIter
    children: List["LoopIterNode"] = field(default_factory=list)


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
        parse lines like

         c loop 0 main 0 -1 |
         sfoa 1 |
         guards goto_symex::\guard#1 goto_symex::\guard#2 |
         lguard goto_symex::\guard#3 |
         linput main::1::res!0@1 oa_constant::!0 |
         lmisc_input main::1::num!0@1 main::1::num!0@1#2 |
         linner_input main::1::res!0@1 main::1::res!0@1#5 |
         linner_output main::1::res!0@1 main::1::res!0@1#6 |
         loutput main::1::res!0@1 main::1::res!0@1#7
        """
        id_part, sfoa_part, guards_part, lguard_part, linput_part, lmisc_input_part, \
        linner_input_part, linner_output_part, loutput_part = line[len(
            "c loop "):].split(" | ")
        id_str, func_str, nr_str, parent_loop = id_part.split(" ")
        lguard_var = self._parse_variables(lguard_part, remove_first=True)
        iter = LoopIter(None, self._parse_guards(guards_part[len("guards "):]),
                        int(id_str), func_str, int(nr_str), "1" in sfoa_part,
                        None if parent_loop == "-1" else int(parent_loop),
                        lguard_var[0] if lguard_var else None,
                        *(self._parse_mapping_tuple(part) for part in
                          (linput_part, linner_input_part, lmisc_input_part, linner_output_part, loutput_part)))
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
        return self._parse_mapping_tuple(part)[1]

    def _parse_mapping_tuple(self, part: str) -> Tuple[List[VarNode], NameMapping]:
        """
        Parses "TAG VAR_1 ACTUAL_VAR_1 … VAR_N ACTUAL_VAR_N" into a name mapping

        Only valid if all variable lines are parsed
        """
        mapping: Dict[str, Clause] = {}
        nodes: List[VarNode] = []
        parts = part[part.find(" ") + 1:].split(" ")
        if (not parts[0] and len(parts) == 1) or " " not in part:
            return [], NameMapping()
        assert len(parts) % 2 == 0
        for i in range(0, len(parts), 2):
            node = self.get_var_node(parts[i + 1])
            nodes.append(node)
            variables = [parse_variable(v) for v in node.raw_sat]
            if variables:
                assert variables, parts[i + 1]
                mapping[parts[i]] = variables
        return nodes, NameMapping(mapping)

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

        self.rec_nodes[func_id] = RecursionNode(func_id, ApplicableCNF(inputs, outputs, [], []), [],
                                                fully_over_approximate=False)

    def get_loops_layered(self) -> List[List[LoopIter]]:
        """ Loops in layers. First layer contains only loops that have no children, … """
        loop_children: Dict[int, Set[int]] = defaultdict(set)
        loop_ids: Set[int] = set()
        for loop_iter in self.loop_iters:
            if loop_iter.parent_loop:
                loop_children[loop_iter.parent_loop].add(loop_iter.id)
            if loop_iter.id not in loop_children:
                loop_children[loop_iter.id] = set()

        res: List[List[LoopIter]] = []

        while loop_children:
            layer = [self.loop_iters[loop] for loop, children in loop_children.items() if not children]
            for loop in layer:
                if loop.parent_loop:
                    loop_children[loop.parent_loop].remove(loop.id)
                del loop_children[loop.id]
            res.append(layer)
        return res

    @staticmethod
    def _find_origins(start_nodes: List[Node], dont_cross: Set[Node] = None) -> Set[Origin]:
        """
        Find all nodes that the start nodes are related to (and themselves) and return their combined
        origins
        """
        origins: Set[Origin] = set()

        def visit(node: Node):
            origins.update(node.origin)
            if not dont_cross or node not in dont_cross:
                return node.neighbors

        bfs(start_nodes, visit)
        return origins

    def _create_recursion_graph(self, consumed: Consumed) -> List[RecursionNode]:
        """
        Creates the proper recursion nodes and remove the deps and children from the graph that belong
        to a recursion node
        """
        # assert not self._finished_rec_nodes
        rec_children: Set[RecursionChild] = set(self.rec_children)
        deps: Set[Dep] = set(self.cnf.deps)
        clauses: Set[int] = set(range(len(self.cnf.clauses)))

        for node in self.rec_nodes.values():
            if node in consumed.consumed_nodes:
                continue
            # given a recursion node, find
            #   - the clauses and deps that belong to it
            #   - find its children

            node_deps: Set[Dep] = set()
            node_children: Set[RecursionChild] = set()
            node_clauses: Set[int] = set()

            # vars that are related to the return
            return_vars = [self.get_sat_node(var) for var in node.acnf.output.combined_clause()]

            omitted = consumed.combined()
            for origin in self._find_origins(return_vars):
                if origin in omitted:
                    continue
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

    def process_recursion_graph(self, consumed: Consumed, dep_policy: DepGenerationPolicy,
                                compute_max_vars: bool = True) -> RecursionProcessingResult:
        # todo: currently only uses the default config for variability over approximation
        from dsharpy.counter import State
        rec = self._create_recursion_graph(consumed)
        state = RecursionProcessingResult(dep_policy)
        DepEqClassesRecursionProcessor(rec, state).run()
        if compute_max_vars:
            MaxVariabilityRecursionProcessor(rec, lambda c: State(c).compute(), state).run()
        return state

    @staticmethod
    def _func_name_of_loop_iter(loop_iter: LoopIter) -> str:
        return f"loop {loop_iter.id}"  # all other recursions do not contain a space, therefore its unique

    def create_loop_iter_tree(self) -> List[LoopIterNode]:
        nodes: Dict[int, LoopIterNode] = {}
        for loop_child in self.loop_iters:
            nodes[loop_child.id] = LoopIterNode(loop_child, [])
        for loop_iter in self.loop_iters:
            if loop_iter.parent_loop:
                nodes[loop_iter.parent_loop].children.append(nodes[loop_iter.id])
        return [node for node in nodes.values() if not node.children]

    def process_loop_iters(self) -> Consumed:
        consumed = Consumed()
        for node in self.create_loop_iter_tree():
            child, cons = self.process_loop_iter_tree_node(node)
            self.rec_children.append(child)
            consumed.update(cons)
        return consumed

    def process_loop_iter_tree_node(self, loop_iter_node: LoopIterNode) -> Tuple[RecursionChild, Consumed]:
        consumed = Consumed()
        children: List[RecursionChild] = []
        for loop_child in loop_iter_node.children:
            child, cons = self.process_loop_iter_tree_node(loop_child)
            consumed.update(cons)
            children.append(child)
        return self.process_loop_iter(loop_iter_node.iter, children, consumed)

    def process_loop_iter(self, loop_iter: LoopIter, loop_children: List[RecursionChild],
                          consumed_by_children: Consumed) \
            -> Tuple[RecursionChild, Consumed]:

        consumed = consumed_by_children | Consumed()
        consumed.consumed_children.update(loop_children)

        omitted = consumed.combined()

        def var_nodes_to_mapping(nodes: List[VarNode]) -> Dict[str, Variables]:
            return {node.name.split("#")[0]: [parse_variable(raw) for raw in node.raw_sat] for node in nodes}

        id: str = self._func_name_of_loop_iter(loop_iter)

        last_iter_guard_sat_vars: List[Node] = loop_iter.guard.sat_vars if loop_iter.guard else []

        children: Set[RecursionChild] = set()  # we do not support nested loops for now,
        # but we could still have rec children
        clauses: Set[int] = set()
        deps: Set[Dep] = set()

        def parse_back(start: List[VarNode], border: Set[Node], omit: Set[Origin] = None) \
                -> Tuple[Set[Dep], Set[RecursionChild], Set[int]]:
            """ parse the origins """
            children_: Set[RecursionChild] = set()
            clauses_: Set[int] = set()
            deps_: Set[Dep] = set()
            for origin in self._find_origins([v for s in start for v in s.sat_vars],
                                             border):
                if omit and origin in omit:
                    continue
                if isinstance(origin, Dep):
                    deps_.add(origin)
                elif isinstance(origin, RecursionChild):  # a real recursion child, not related to loops
                    children_.add(origin)
                else:
                    assert isinstance(origin, int)
                    clauses_.add(origin)
            return deps_, children_, clauses_

        # combined_input = loop_iter.inp + loop_iter.last_iter_input

        prev_guards = [g for g, pos in loop_iter.guards]

        last_guard_var: Optional[int] = loop_iter.guard.sat_vars[0].sat_var \
            if loop_iter.guard else None

        # tackle clauses like (with 1 and 2 being prev guards and 4 being that last guard)
        #  1 -5 0
        #  2 -5 0
        #  4 -5 0
        #  -1 -2 -4 5 0
        prev_guard_sat_vars = {g.sat_vars[0].sat_var for g, pos in loop_iter.guards if g.sat_vars}
        prev_guard_combining_clause_node: Optional[Node] = None
        prev_guard_border_nodes: List[Node] = []
        prev_guard_border_origins: Set[Origin] = set()
        if loop_iter.guard and (sv := loop_iter.guard.sat_vars):
            for neighbor in sv[0].neighbors:
                for origin in neighbor.origin:
                    if isinstance(origin, int):  # a clause
                        clause = self.cnf.clauses[origin]
                        if any(-var in clause for var in prev_guard_sat_vars):  # we found our offending node
                            prev_guard_combining_clause_node = neighbor
                            break
        if prev_guard_combining_clause_node:
            # we found it the last clause in the above comment
            # get the "5"
            connecting_nodes = [node for node in prev_guard_combining_clause_node.neighbors
                                if node.sat_var not in prev_guard_sat_vars and
                                loop_iter.guard and [node] != loop_iter.guard.sat_vars]
            for connecting_node in connecting_nodes:
                prev_guard_border_nodes.extend(connecting_node.neighbors)
                prev_guard_border_origins.update(x for neighbor in connecting_node.neighbors for x in neighbor.origin)

        combined_inner_input: List[VarNode] = loop_iter.inner_input[0] + loop_iter.misc_input[0]

        border = set(
            [v for var in (combined_inner_input + prev_guards) for v in var.sat_vars] + prev_guard_border_nodes)

        # the inner loop part
        deps, children, clauses = parse_back(loop_iter.inner_output[0],
                                             border | set(last_iter_guard_sat_vars) | omitted)

        real_clauses = [self.cnf.clauses[i] for i in clauses]

        # the guard part
        deps_guard, children_guard, clauses_guard = parse_back([loop_iter.guard], border,
                                                               deps | children | clauses | prev_guard_border_origins | omitted) \
            if loop_iter.guard \
            else (set(), set(), set())
        real_clauses_guard = [self.cnf.clauses[i] for i in clauses_guard]

        consumed.update(Consumed(children, deps, clauses))
        consumed.update(Consumed(children_guard, deps_guard, clauses_guard))

        # we then construct the following function
        #
        # f(input):
        #   guard_part
        #   with condition guard:   # add guard to all deps and rec children
        #       inner part
        #       output' = f(output)
        #   output'' = guard ? output' : input
        #   return output''
        # this is a equivalent to the loop but can be evaluated by the existing recursion graph code
        # → we can throw out all loop handling code besides this transformation
        #   … and handling just recursion should should be simpler
        # todo: maybe create recursion nodes that contain the additional information

        new_vars: List[int] = []

        def new_var() -> int:
            """ introduce a new SAT variable that is larger than the existing """
            new_variable = self.cnf.nv + len(new_vars) + 1
            new_vars.append(new_variable)
            return new_variable

        final_input_mapping = dict(loop_iter.inner_input[1])
        final_input_mapping.update(loop_iter.misc_input[1])
        final_children: List[RecursionChild] = []

        cnf = DCNF()
        # add the guard_part
        cnf.extend(real_clauses_guard)
        for dep in deps_guard:
            cnf.add_dep(dep)
        for child in children_guard:
            final_children.append(child)
        # add the inner part
        for dep in deps:
            if last_guard_var:
                if last_guard_var:
                    dep = dep.add_constraint(last_guard_var)
                    consumed.consumed_deps.add(dep)
                cnf.add_dep(dep)
        for l in [children, loop_children]:
            for child in l:
                if last_guard_var:
                    child = child.add_constraint(len(self.rec_children), last_guard_var)
                    self.rec_children.append(child)
                    consumed.consumed_children.add(child)
                final_children.append(child)
        if last_guard_var:
            cnf.extend([clause + [-last_guard_var] for clause in real_clauses])
        else:
            cnf.extend(real_clauses)
        # add the function call
        #    output' = f(output, misc)
        new_output: Dict[str, Variables] = {name: [(new_var() if isinstance(var, int) else var) for var in vars]
                                            for name, vars in loop_iter.inner_output[1].items()}
        new_child = RecursionChild(self.rec_nodes, len(self.rec_children), id,
                                   loop_iter.inner_input[1] | loop_iter.misc_input[1],
                                   NameMapping(new_output), {last_guard_var} if last_guard_var else set())
        # self.rec_children.append(new_child)
        final_children.append(new_child)

        # create the final output
        #    output'' = guard ? output' : input

        # first create a new version of the outputs
        final_output = {name: [new_var() for var in vars]
                        for name, vars in loop_iter.inner_output[1].items()}
        # guard  => (output''_i <=> output'_i)
        #    ==   (-guard v -output''_i v output'_i) (-guard v -output''_i v output'_i)
        # -guard => (output''_i <=> output_i)
        #    ==   (-guard v -output''_i v output_i)  (-guard v -output'_i v output_i)
        # later:
        #    return consumed_X

        guard = last_guard_var if last_guard_var else new_var()

        def assign_guarded(g: int, right: Mapping[str, Variables]):
            for name, vars in final_output.items():
                other_vars = right[name]
                for var, other_var in zip(vars, other_vars):
                    if other_var is True:
                        cnf.append([-g, var])
                    elif other_var is False:
                        cnf.append([-g, -var])
                    else:
                        cnf.append([-g, var, -other_var])
                        cnf.append([-g, -var, other_var])

        assign_guarded(guard, new_output)
        assign_guarded(-guard, loop_iter.inner_output[1])

        if last_guard_var:
            self.cnf.clauses.append([guard])

        for dep in cnf.deps:
            self.cnf.add_dep(dep)
        for clause in cnf:
            self.cnf.append(clause)
            consumed.consumed_clauses.add(len(self.cnf.clauses) - 1)
        consumed.consumed_children.update(final_children)

        node = RecursionNode(id, ApplicableCNF(NameMapping(final_input_mapping),
                                               NameMapping(final_output), cnf.clauses, cnf.deps),
                             children=final_children, fully_over_approximate=loop_iter.fully_over_approximate)
        self.rec_nodes[node.id] = node
        consumed.consumed_nodes.add(node)

        child = RecursionChild(self.rec_nodes, len(self.rec_children), id,
                               loop_iter.input[1] | loop_iter.misc_input[1], loop_iter.output[1],
                               loop_iter.guard_conjunction())
        return child, consumed

    @classmethod
    def parse_graph(cls, raw_lines: List[str], dep_policy: DepGenerationPolicy, ind_var_prefix: str = None,
                    use_latest_ind_var: bool = True, compute_max_vars: bool = True) -> "Graph":
        graph = Graph()
        lines = []
        recursion_child_lines: List[str] = []
        recursion_node_lines: List[str] = []
        loop_lines: List[str] = []
        for line in raw_lines:
            line = line.strip()
            if Graph.is_sat_line(line):
                graph._parse_sat_line(line)
                lines.append(line)
            elif Graph.is_var_line(line):
                graph._parse_var_line(line)
                lines.append(line)
            elif Graph.is_loop_line(line):
                loop_lines.append(line)
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
        for line in loop_lines:
            graph._parse_loop_line(line)
        graph.update_var_deps()
        if ind_var_prefix:
            ind = graph.find_ind_vars(ind_var_prefix, use_latest_ind_var)
            graph.cnf.add_ind(*ind)

        consumed = graph.process_loop_iters()

        proc_res = graph.process_recursion_graph(consumed, dep_policy, compute_max_vars)
        for rec_child in graph.rec_children:
            deps, clauses = proc_res.to_dep(rec_child, graph.cnf.nv + 1)
            for dep in deps:
                graph.cnf.add_dep(dep)
            graph.cnf.extend(clauses)
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
