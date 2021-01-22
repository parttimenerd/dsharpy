"""
This module is based on the pysat.formula module to provide a simple interface to CNF formulas with
D#SAT specific comments.
"""
import copy
import math
import re
import subprocess
import sys
import tempfile
from abc import abstractmethod
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import List, Set, Tuple, Optional, Union, Iterable, Deque

from pysat.formula import CNF

from dsharpy.util import binary_path, empty, random_bool, random_split


@dataclass(frozen=True)
class Dep:

    param: Set[int]
    ret: Set[int]
    constraint: Set[int] = field(default_factory=set)

    def empty(self) -> bool:
        return not len(self.ret)

    def to_comment(self) -> str:
        if self.empty():
            return f"c empty dep from {' '.join(map(str, self.param))}"
        return f"c dep {' 0 '.join(' '.join(map(str, x)) for x in [self.param, self.ret, self.constraint])}"

    @classmethod
    def from_comment(cls, comment: str) -> "Dep":
        assert comment.startswith("c dep ")
        assert comment.count(" 0 ") >= 1
        param_part, ret_part, *constraint_part = comment[len("c dep "):].split(" 0 ", maxsplit=2)

        def split(part: str) -> Set[int]:
            return {int(i) for i in part.split(" ") if len(i) and i != "0"}

        return Dep(split(param_part), split(ret_part), split(constraint_part[0]) if len(constraint_part) == 1 else set())

    def __str__(self) -> str:
        return f"{self.param} ~{self.constraint}~> {self.ret}"

Deps = List[Dep]

Independents = List[Set[Tuple[int, int]]]


class DCNF(CNF):

    def __init__(self, from_file=None, from_fp=None, from_string=None, from_clauses: List[List[int]] = None,
                 from_aiger=None,
                 ind: Set[int] = None, deps: Deps = None, independents: Independents = None):
        super().__init__(from_file, from_fp, from_string, from_clauses or [], from_aiger, comment_lead=['c'])
        self.ind = ind or set()
        self.deps: Deps = deps or []
        self.independents = independents or []
        self._update_from_comments(self.comments)

    def _update_comments(self, new_ind: Iterable[int], new_deps: Deps, new_indies: Independents):
        self.comments.append(self.format_ind_comment(new_ind))
        self.comments.extend(dep.to_comment() for dep in new_deps)
        self.comments.extend(f"c indies {' '.join(map(lambda s: f'{s[0]} {s[1]}', i))}" for i in new_indies)

    def _clean_up_comments(self):
        """ Remove all ind and deps related comments """
        self.comments = [c for c in self.comments if not self._is_special_comment(c)]

    def reset_comments(self):
        self._clean_up_comments()
        self._update_comments(self.ind, self.deps, self.independents)

    def _parse_comments(self, comments: List[str]) -> Tuple[Set[int], Deps, Independents]:
        ind: Set[int] = set()
        deps: Deps = []
        indies = []
        for c in comments:
            if not self._is_special_comment(c):
                continue
            ints: List[int] = []
            try:
                ints = list(int(e) for e in c[6:].split(" "))
            except ValueError as ex:
                print(c)
                exit(1)
            if ints[-1] == 0:
                ints = ints[:-1]
            if c.startswith("c ind "):
                ind.update(ints)
            elif c.startswith("c dep "):
                deps.append(Dep.from_comment(c))
            else:
                tmp = set()
                for i in range(0, len(ints), 2):
                    tmp.add((ints[i], ints[i + 1]))
                indies.append(tmp)
        return ind, deps, indies

    def _update_from_comments(self, comments: List[str], ignore_self: bool = False):
        if not comments:
            return
        combined = ([] if ignore_self else self.comments) + comments
        ind, deps, indies = self._parse_comments(combined)
        self.comments.clear()
        self.add_ind(*ind)
        for dep in deps:
            self.add_dep(dep)
        self.independents.extend(indies)
        self.comments.extend(set(x for x in combined if not self._is_special_comment(x)))

    def add_ind(self, *ind: int):
        if not ind:
            return
        diff = set(ind) - self.ind
        self.ind.update(diff)
        self.comments.append(self.format_ind_comment(diff))
        self.nv = max(self.nv, max(diff))

    def add_dep(self, dep: Dep):
        self.deps.append(dep)
        self.comments.append(dep.to_comment())
        self.nv = max(self.nv, max(max(dep.param, default=0), max(dep.ret, default=0), max(dep.constraint, default=0)))

    @staticmethod
    def format_ind_comment(ind: Iterable[int]) -> str:
        if not empty(ind):
            return f"c ind {' '.join(map(str, ind))} 0"
        return "c ind 0"

    @staticmethod
    def _is_special_comment(comment: str) -> bool:
        return comment.startswith("c ind ") or comment.startswith("c dep ") or comment.startswith("c par ")

    def from_fp(self, file_pointer, comment_lead=['c']):
        super().from_fp(file_pointer, comment_lead)
        self.ind = set()
        self.deps = []
        self._update_from_comments(self.comments, ignore_self=True)

    def copy(self) -> 'DCNF':
        """ Copy the CNF """
        cnf = DCNF()
        cnf.nv = self.nv
        cnf.clauses = copy.deepcopy(self.clauses)
        cnf.comments = copy.deepcopy(self.comments)
        cnf.ind = copy.deepcopy(self.ind)
        cnf.deps = copy.deepcopy(self.deps)
        cnf.independents = copy.deepcopy(self.independents)
        return cnf

    def shallow_copy(self) -> 'DCNF':
        cnf = DCNF()
        cnf.nv = self.nv
        cnf.clauses = copy.copy(self.clauses)
        cnf.comments = copy.copy(self.comments)
        cnf.ind = copy.copy(self.ind)
        cnf.deps = copy.copy(self.deps)
        cnf.independents = copy.copy(self.independents)
        return cnf

    def really_shallow_copy(self) -> 'DCNF':
        cnf = DCNF()
        cnf.nv = self.nv
        cnf.clauses = self.clauses
        cnf.comments = self.comments
        cnf.ind = self.ind
        cnf.deps = self.deps
        cnf.independents = self.independents
        return cnf

    def weighted(self):
        raise NotImplementedError()

    def negate(self, topv=None):
        raise NotImplementedError()

    def get_comment(self, tag: str) -> Optional[str]:
        """ Get the first comment that starts with "c tag " """
        for comment in self.comments:
            if comment[2:].startswith(tag + " "):
                return comment
        return None

    def get_dep_relations(self) -> List[Tuple[int, int]]:
        return [(a, b) for a_s, bs in self.deps.items() for b in bs for a in a_s]

    @staticmethod
    def load(path: Path) -> 'DCNF':
        cnf = DCNF()
        cnf.from_file(str(path))
        return cnf

    @staticmethod
    def load_string(string: str) -> 'DCNF':
        cnf = DCNF()
        cnf.from_string(string)
        return cnf

    def set_deps(self, deps: Deps) -> "DCNF":
        ret = self.really_shallow_copy()
        ret.deps = deps
        ret.comments.clear()
        ret._update_comments(self.ind, ret.deps, self.independents)
        return ret

    def set_ind(self, new_ind: Iterable[int]) -> "DCNF":
        ret = self.really_shallow_copy()
        ret.comments.clear()
        ret.ind.clear()
        ret._update_comments(new_ind, self.deps, self.independents)
        return ret


def blast_xor(*vars: int) -> List[List[int]]:
    """
    Blast the xor of the passed vars.
    Only use it for small number of vars
    """
    vars = list(vars)
    if len(vars) <= 1:
        return [vars]
    return [vars] + [[-v2 for v2 in vars if v2 != v] + [v] for v in vars]


def sum_is_one2(a: int, b: int) -> List[List[int]]:
    """
    a and b are boolean variables

    a + b = 1 ←→ a xor b ←→ (a → -b) and (-a → b)
    """
    return [[-a, -b], [a, b]]


def sum_is_one4(a: int, b: int, c: int, d: int, new_var1: int, new_var2: int) -> List[List[int]]:
    """
    :param new_var1: new variable to use
    """
    return blast_xor(new_var1, a, b) + blast_xor(new_var2, c, d) + sum_is_one2(a, b) + [[-a, -b], [-c, -d]]


def sat(cnf: CNF) -> bool:
    try:
        from pycryptosat import Solver
        s = Solver()
        s.add_clauses(cnf.clauses)
        return s.solve()[0]
    except ModuleNotFoundError:
        with NamedTemporaryFile() as f:
            cnf.to_file(f.name)
            return subprocess.check_output(f"{binary_path('cryptominisat5')} --verb 0 {f.name} || true",
                                           shell=True).decode().splitlines()[0] == "s SATISFIABLE"


def _parse_amc_out(cnf: CNF, out: str, err: str) -> Optional[float]:
    try:
        [mul_base, exponent] = re.split("\\*\\*|\\^", out.split("Number of solutions is:")[1])
        [multiplier, base] = re.split("[*x]", mul_base)
        multiplier = float(multiplier)
        base = float(base)
        exponent = float(exponent.split("\n")[0])
        solutions = multiplier * base ** exponent
        return solutions
    except IndexError as ex:
        print("--- Error ---")
        print(out)
        print(err)
        cnf.to_fp(sys.stdout)
        return None


def count_sat(cnfs: Union[List[CNF], CNF], epsilon: float = 0.8, delta: float = 0.2, forcesolextension: bool = False,
              trim: bool = True) \
        -> Union[List[Optional[float]], Optional[float]]:
    """
    Run ApproxMC with the passed parameters. If multiple CNFs are passed, then these are executed in parallel.
    """
    options = {
        "epsilon": epsilon,
        "delta": delta,
        "forcesolextension": int(forcesolextension)
    }
    is_single = isinstance(cnfs, CNF)
    if is_single:
        cnfs = [cnfs]
    try:
        with tempfile.TemporaryDirectory() as folder:
            files = []
            used_cnfs = []
            for i, cnf in enumerate(cnfs):
                file = f"{folder}/{i}.cnf"
                if trim:
                    cnf = CNFGraph(cnf).sub_cnf()
                used_cnfs.append(cnf)
                cnf.to_file(file)
                # cnf.to_fp(sys.stdout)
                files.append(file)
            processes = [subprocess.Popen(
                f"{binary_path('approxmc4')} {file} {' '.join(f'--{k} {v}' for k, v in options.items())}",
                shell=True,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE) for file in files]
            ret = []
            for i, process in enumerate(processes):
                out, err = process.communicate()
                ret.append(_parse_amc_out(used_cnfs[i], out.decode(), err.decode()))
            return ret[0] if is_single else ret
    except:
        # fall bock onto the old ApproxMC
        # if _use_newest:
        #     return count_sat(cnfs, epsilon=epsilon, delta=delta, forcesolextension=forcesolextension,
        #                      _use_newest=False)
        raise


def parse_ind_from_comments(cnf: CNF) -> Iterable[int]:
    ind: Set[int] = set()
    for comment in cnf.comments:
        if comment.startswith("c ind "):
            try:
                ind.update(set(int(p) for p in comment[6:].split(" ") if p != "0"))
            except BaseException as ex:
                print(comment, file=sys.stderr)
                raise
    return ind


class CNFGraph:

    def __init__(self, cnf: CNF):
        self.cnf = cnf
        self.var_to_clauses: List[List[int]] = [[] for i in range(0, cnf.nv + 1)]
        for i, clause in enumerate(cnf.clauses):
            for var in clause:
                self.var_to_clauses[abs(var)].append(i)

    def sub_cnf(self, relevant_vars: Iterable[int] = None, copy_comments: bool = True) -> CNF:
        relevant_vars = relevant_vars or parse_ind_from_comments(self.cnf)
        if empty(relevant_vars):
            return CNF()
        visited_clauses: Set[int] = set()
        visited_vars: Set[int] = set()

        deq: Deque[int] = deque()  # a deque of vars
        deq.extend(relevant_vars)
        while len(deq) > 0:
            top = deq.pop()
            if top in visited_vars:
                continue
            visited_vars.add(top)
            deq.extendleft(set(abs(var) for clause in self.clause_for_var(top) for var in self.cnf.clauses[clause]))
            visited_clauses.update(self.clause_for_var(top))

        cnf = CNF()
        if copy_comments:
            cnf.comments = self.cnf.comments
        cnf.from_clauses([self.cnf.clauses[c] for c in visited_clauses])
        cnf.nv = max(cnf.nv, max(relevant_vars))
        return cnf

    def clause_for_var(self, var: int) -> List[int]:
        if var < len(self.var_to_clauses):
            return self.var_to_clauses[var]
        return []


def trim_dcnf(cnf: DCNF, anchors: Iterable[int] = None) -> DCNF:
    """ Removes all clauses that are independent from the passed vars or cnf.ind """
    return trim_dcnf_graph(CNFGraph(cnf), anchors)


def trim_dcnf_graph(graph: CNFGraph, anchors: Iterable[int] = None) -> DCNF:
    cnf = graph.cnf
    assert isinstance(cnf, DCNF)
    new_cnf = graph.sub_cnf(anchors or cnf.ind, copy_comments=True)
    new_dcnf = DCNF(from_clauses=new_cnf.clauses, ind=cnf.ind, deps=cnf.deps, independents=cnf.independents)
    new_dcnf.comments = cnf.comments
    assert new_dcnf.independents == cnf.independents and new_dcnf.ind == cnf.ind
    return new_dcnf


@dataclass
class XOR:
    variables: List[int]

    def dimacs(self) -> List[List[int]]:
        return blast_xor(*self.variables)

    def __str__(self) -> str:
        return "⊻".join(map(str, self.variables))

    def randomize(self) -> "XOR":
        """ Randomize the signs of the variables """
        return XOR([(-1 if random_bool() else 1) * v for v in self.variables])

@dataclass
class XORs:

    xors: List[XOR]

    def to_dimacs(self):
        return [c for xor in self.xors for c in xor.dimacs()]

    def variables(self) -> Set[int]:
        return set(abs(x) for xor in self.xors for x in xor.variables)

    def count_sat(self, **kwargs):
        dcnf = DCNF(from_clauses=self.to_dimacs())
        return count_sat(dcnf.set_ind(dcnf.set_ind(self.variables())), **kwargs)

    def __str__(self):
        return " ∧ ".join(map(str, self.xors))


class XORGenerator:
    """ Generate xors for a specific"""

    @abstractmethod
    def generate(self, variables: List[int], variability: float) -> XORs:
        """
        Generate a list of xors which constraint the variables, so that the resulting variability
        of the variables + constraints is in bits as given
        """
        pass


class OverapproxXORGenerator(XORGenerator):

    def generate(self, variables: List[int], variability: float) -> XORs:
        return self._generate(variables, math.ceil(variability))

    @abstractmethod
    def _generate(self, variables: List[int], variability: int) -> XORs:
        pass


class FullyRandomXORGenerator(OverapproxXORGenerator):
    """
    Idea:
     Generate $restricted_bits$ number of XOR clauses that contain each variable with probability 0.5
    """

    def _create_random_xor(self, variables: List[int]) -> XOR:
        return XOR([v for v in variables if random_bool()]).randomize()

    def _generate(self, variables: List[int], variability: int) -> XORs:
        restricted_bits = len(variables) - variability
        return XORs([self._create_random_xor(variables) for i in range(restricted_bits)])


class RangeSplitXORGenerator(OverapproxXORGenerator):
    """
    Idea:
     Split variable set into $restricted_bits$ disjoint subsets, each of them will become an XOR
    """

    def _generate(self, variables: List[int], variability: int) -> XORs:
        return XORs([XOR(part).randomize() for part in random_split(variables, len(variables) - variability, min_size=1)])