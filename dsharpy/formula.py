"""
This module is based on the pysat.formula module to provide a simple interface to CNF formulas with
D#SAT specific comments.
"""
import copy
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import List, Dict, Set, Tuple, Optional, Union

from pysat.formula import CNF

from dsharpy.util import binary_path

Deps = Dict[int, Set[int]]
Independents = List[Set[Tuple[int, int]]]


class DCNF(CNF):

    def __init__(self, from_file=None, from_fp=None, from_string=None, from_clauses: List[List[int]] = None,
                 from_aiger=None,
                 ind: Set[int] = None, deps: Deps = None, independents: Independents = None):
        super().__init__(from_file, from_fp, from_string, from_clauses or [], from_aiger, comment_lead=['c'])
        self.ind = ind or set()
        self.deps = deps or {}
        self.independents = independents or []
        self._update_from_comments(self.comments)

    def _update_comments(self, new_ind: List[int], new_deps: Deps, new_indies: Independents):
        self.comments.append("c ind " + " ".join(map(str, new_ind)) + " 0")
        self.comments.extend(f"c dep {a} {' '.join(map(str, b))} 0" for a, b in new_deps)
        self.comments.extend(f"c indies {' '.join(map(lambda s: f'{s[0]} {s[1]}', i))}" for i in new_indies)

    def _clean_up_comments(self):
        """ Remove all ind and deps related comments """
        self.comments = [c for c in self.comments if not self._is_special_comment(c)]

    def reset_comments(self):
        self._clean_up_comments()
        self._update_comments(self.ind, self.deps, self.independents)

    def _parse_comments(self, comments: List[str]) -> Tuple[Set[int], Deps, Independents]:
        ind = set()
        deps = {}
        indies = []
        for c in comments:
            if not self._is_special_comment(c):
                continue
            ints = list(int(e) for e in c[6:].split(" ") if e != "0")
            if c.startswith("c ind "):
                ind.update(ints)
            elif c.startswith("c dep "):
                a = ints[0]
                if a not in deps:
                    deps[a] = set()
                deps[a].update(ints[1:])
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
        ind, dep, indies = self._parse_comments(combined)
        self.comments.clear()
        self.add_ind(*ind)
        for a in dep:
            self.add_dep(a, dep[a])
        self.independents.extend(indies)
        self.comments.extend(set(x for x in combined if not self._is_special_comment(x)))

    def add_ind(self, *ind: int):
        diff = set(ind) - self.ind
        self.ind.update(diff)
        self.comments.append(f"c ind {' '.join(map(str, diff))} 0")
        self.nv = max(self.nv, max(diff))

    def add_dep(self, a: int, bs: Set[int]):
        to_add = []
        if a not in self.deps:
            self.deps[a] = bs
            to_add = bs
        else:
            old = self.deps[a]
            for b in bs:
                if b not in old:
                    old.add(b)
                    to_add.append(b)
        self.comments.append(f"c dep {a} {' '.join(map(str, to_add))} 0")
        self.nv = max(self.nv, max(a, max(to_add)))

    @staticmethod
    def _is_special_comment(comment: str) -> bool:
        return comment.startswith("c ind ") or comment.startswith("c dep ") or comment.startswith("c par ")

    def from_fp(self, file_pointer, comment_lead=['c']):
        super().from_fp(file_pointer, comment_lead)
        self.ind = set()
        self.deps = {}
        self._update_from_comments(self.comments, ignore_self = True)

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
        return [(a, b) for a, bs in self.deps.items() for b in bs]

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


def blast_xor(*vars: int) -> List[List[int]]:
    """
    Blast the xor of the passed vars.
    Only use it for small number of vars
    """
    return [list(vars)] + [[-v2 for v2 in vars if v2 != v] + [v] for v in vars]


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


def _parse_amc_out(out: str, err: str) -> Optional[float]:
    try:
        [mul_base, exponent] = re.split("\\*\\*|\\^", out.split("Number of solutions is:")[1])
        [multiplier, base] = re.split("\\*|x", mul_base)
        multiplier = float(multiplier)
        base = float(base)
        exponent = float(exponent.split("\n")[0])
        solutions = multiplier * base ** exponent
        return solutions
    except IndexError as ex:
        print("--- Error ---")
        print(out)
        print(err)
        return None


def count_sat(cnfs: Union[List[DCNF], DCNF], epsilon: float = 0.8, delta: float = 0.2, forcesolextension: bool = False,
              _use_newest: bool = True) -> Union[List[Optional[float]], Optional[float]]:
    """
    Run ApproxMC with the passed parameters. If multiple CNFs are passed, then these are executed in parallel.
    """
    options = {}
    if _use_newest:
        # TODO: add options and recompile ApproxMC4
        options = {
            "epsilon": epsilon,
            "delta": delta,
            "forcesolextension": int(forcesolextension)
        }
    else:
        options = {

        }
    is_single = isinstance(cnfs, DCNF)
    if is_single:
        cnfs = [cnfs]
    try:
        with tempfile.TemporaryDirectory() as folder:
            files = []
            for i, cnf in enumerate(cnfs):
                file = f"{folder}/{i}.cnf"
                cnf.to_file(file)
                #cnf.to_fp(sys.stderr)
                files.append(file)
            processes = [subprocess.Popen(
                f"{binary_path('approxmc4' if _use_newest else 'approxmc2')} {file} {' '.join(f'--{k} {v}' for k, v in options.items())}",
                shell=True,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE) for file in files]
            ret = []
            for process in processes:
                out, err = process.communicate()
                ret.append(_parse_amc_out(out.decode(), err.decode()))
            return ret[0] if is_single else ret
    except:
        # fall bock onto the old ApproxMC
        # if _use_newest:
        #     return count_sat(cnfs, epsilon=epsilon, delta=delta, forcesolextension=forcesolextension,
        #                      _use_newest=False)
        raise