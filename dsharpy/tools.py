""" Utilities not directly related to formulas or CNFs """
import logging
import math
import os
import re
import shutil
import subprocess
import tempfile
from typing import TYPE_CHECKING, Dict, Set, Tuple, Iterable

from dsharpy.preprocess import preprocess_c_code

from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import List, Union, Any

logging.basicConfig(level=logging.WARNING)


def pprint(x: Any):
    import prettyprinter
    prettyprinter.install_extras(exclude=['ipython', 'ipython_repr_pretty'])
    prettyprinter.pprint(x)


class Tool:
    OUTPUT_PREFIX = "__out"

    def __init__(self, name: str, binary: str):
        self.name = name
        self.binary_path = Path(binary.replace("TOOLS", str(Path(__file__).parent.parent.absolute() / "tools")))
        assert self._check_binary(), f"Binary for {name} ({self.binary_path}) not found"

    def _check_binary(self):
        try:
            subprocess.run([str(self.binary_path), "-h"], check=True, capture_output=False,
                           stdout=subprocess.DEVNULL)
            return True
        except subprocess.CalledProcessError:
            return False

    def _process(self, arguments: List[Any], env_vars: Dict[str, Any], interpreter: str = None,
                 cwd: Path = None) -> str:
        env = os.environ.copy()
        for key, value in env_vars.items():
            env[key] = str(value)
        cmd = ([interpreter] if interpreter else []) + [str(self.binary_path)] + [str(x) for x in arguments]
        logging.info(cmd)
        res = subprocess.run(cmd,
                             stdout=subprocess.PIPE, bufsize=-1, stderr=subprocess.PIPE, env=env,
                             cwd=str(cwd) if cwd else os.getcwd())
        err = res.stderr.decode()
        out = res.stdout.decode()
        if "Failed" in err or "Usage" in err or "ERROR" in err or "exception" in err \
                or " failed" in err or "segmentation fault" in err \
                or "segmentation fault" in out or res.returncode != 0:
            logging.error(out)
            logging.error(err)
            for argument in arguments:
                if str(argument).endswith(".cpp") and isinstance(argument, Path) and argument.exists():
                    logging.error(argument.read_text())
            raise RuntimeError(f"{self.name}: " + err)

        return out

    @staticmethod
    def _preprocess(tmp_dir: Path, code: Union[str, Path]) -> Path:
        code: str = code if isinstance(code, str) else code.read_text()
        with NamedTemporaryFile(suffix=".cpp", dir=tmp_dir, delete=False) as f:
            f.write(preprocess_c_code(code, Tool.OUTPUT_PREFIX).encode())
            f.flush()
            return Path(f.name)


class ModelChecker(Tool):

    def __init__(self, name: str, binary: str, unwind: int, bit_width: int = 32):
        super(ModelChecker, self).__init__(name, binary)
        self.unwind = unwind
        self.bit_width = bit_width
        self._problem_line_re = re.compile('((p cnf)|(c __rel__ p)) [0-9]+ [0-9]+\n')

    def setup_for(self, lc: "LeakageComputer"):
        pass

    def _is_problem_line(self, line: str) -> bool:
        return bool(self._problem_line_re.match(line))

    def _filter_lines(self, lines: List[str]) -> Iterable[str]:
        has_seen_problem_line = False
        for line in lines:
            if not has_seen_problem_line:
                if self._is_problem_line(line):
                    yield line
                    has_seen_problem_line = True
                continue
            if line.startswith("c ") or line.endswith(" 0\n"):
                yield line

    def process(self, tmp_dir: Path, code: Union[str, Path]) -> Path:
        code = Tool._preprocess(tmp_dir, code)
        with NamedTemporaryFile(suffix=".cnf", dir=tmp_dir, delete=False) as f:
            f.writelines(l.encode() for l in self._filter_lines(self._process(self._arguments(code), self._env_vars(code)).splitlines(keepends=True)))
            return Path(f.name)

    def _env_vars(self, code: Path) -> Dict[str, Any]:
        return {}

    def _arguments(self, code: Path) -> List[Any]:
        return []


class CBMCBase(ModelChecker):
    def __init__(self, name: str, unwind: int = 32, bit_width: int = 32):
        super(CBMCBase, self).__init__(name, f"TOOLS/{name}/build/bin/cbmc", unwind, bit_width)

    def setup_for(self, lc: "LeakageComputer"):
        assert not lc.requires_rel()

    def _env_vars(self, code: Path) -> Dict[str, Any]:
        return {}

    def _arguments(self, code: Path) -> List[Any]:
        return [code, f"--{self.bit_width}", "--unwind", self.unwind, "--dimacs", "--partial-loops"]


class CBMC(CBMCBase):

    def __init__(self, unwind: int = 32, bit_width: int = 32):
        super(CBMC, self).__init__("cbmc", unwind, bit_width)


class ModifiedCBMC(CBMCBase):
    """ CBMC with loop and recursion approximation """

    def __init__(self, unwind: int = 32, bit_width: int = 32):
        super(ModifiedCBMC, self).__init__("modified_cbmc", unwind + 2, bit_width)
        assert self.unwind >= 1
        self.real_unwind = unwind
        self.only_rel = False

    def setup_for(self, lc: "LeakageComputer"):
        self.only_rel = lc.requires_rel()

    def _env_vars(self, code: Path) -> Dict[str, Any]:
        return {"REC": self.real_unwind - 1, **({"RELATIONS": "1", "OMIT_SAT": "1"} if self.only_rel else {})}


class LeakageComputer(Tool):

    def __init__(self, name: str, binary: str, output_method: str = "main"):
        super(LeakageComputer, self).__init__(name, binary)
        self.output_method = output_method

    def requires_rel(self) -> bool:
        raise NotImplementedError()

    def process(self, cnf_file: Path) -> float:
        return self._parse_output(self._process(self._arguments(cnf_file), env_vars={}))

    def _arguments(self, cnf_file: Path) -> List[Any]:
        raise NotImplementedError()

    def _parse_output(self, out: str) -> float:
        raise NotImplementedError()


class RelationsCutter(LeakageComputer):

    def __init__(self, output_method: str = "main", input_prefixes: List[str] = None):
        super(RelationsCutter, self).__init__("relationscutter", "TOOLS/relationscutter/build/relationscutter",
                                              output_method)
        self.input_prefixes = input_prefixes or ["symex::nondet"]

    def requires_rel(self) -> bool:
        return True

    def _arguments(self, cnf_file: Path) -> List[Any]:
        return [cnf_file, "--method", self.output_method, "--input", ",".join(self.input_prefixes), "--output",
                Tool.OUTPUT_PREFIX]

    def _parse_output(self, out: str) -> float:
        return float(out.split("Leakage: ")[1].split("\n")[0])


class ApproxFlow(LeakageComputer):
    """
    Reimplementation of ApproxFlow, it is far simpler as the code preprocessing is simpler

    Based on https://github.com/parttimenerd/approxflow/blob/master/ApproxFlow.py
    """

    def __init__(self, output_method: str = "main", epsilon: float = 0.8, delta: float = 0.2):
        super(ApproxFlow, self).__init__("approxflow", "TOOLS/approxmc", output_method)
        self.delta = delta
        self.epsilon = epsilon

    def requires_rel(self) -> bool:
        return False

    def _get_ind_vars(self, cnf_file: Path) -> Set[int]:
        # based on https://github.com/parttimenerd/approxflow/blob/master/ApproxFlow.py
        # search for __out…!i@j#k, and assume only k changes
        re_to_match = re.compile(f"({Tool.OUTPUT_PREFIX}[0-9]*)![0-9]+@[0-9]+#[0-9]+")
        variables: Dict[str, Tuple[int, Set[int]]] = {}
        max_lits = None
        for line in cnf_file.open():
            if line.startswith("c") and (" " + self.output_method + "::") in line:
                match = re_to_match.search(line)
                if match:
                    assert (len(match.groups()) == 1)
                    variable, ijk = match.group(0).split(Tool.OUTPUT_PREFIX, maxsplit=1)[1].split("!", maxsplit=1)
                    new_k = int(ijk.split("#")[1])
                    old_k = variables[variable][0] if variable in variables else -1
                    sat_vars = {abs(int(var)) for var in line.split()[2:] if var.lower() not in ["true", "false"]}
                    if new_k > old_k:
                        variables[variable] = (new_k, sat_vars)
                    if new_k == old_k:
                        variables[variable][1].update(sat_vars)
        return {x for _, v in variables.items() for x in v[1]}

    def _arguments(self, cnf_file: Path) -> List[Any]:
        with NamedTemporaryFile(suffix=".cnf", dir=cnf_file.parent, delete=False) as f:
            shutil.copy(cnf_file, f.name)
            with Path(f.name).open("a") as of:
                of.write(f"c ind {' '.join(map(str, self._get_ind_vars(cnf_file)))} 0\n")
            return ["--input", f.name]

    def _parse_output(self, out: str) -> float:
        [multiplier, power] = out.split("Number of solutions is:")[1].split("\n")[0].split("*", 1)
        [base, exponent] = power.split("**")
        multiplier = int(multiplier)
        base = int(base)
        exponent = int(exponent)
        solutions = multiplier * base ** exponent
        return math.log(solutions, 2)


def process(model_checker: ModelChecker, leakage_computer: LeakageComputer, code: Union[str, Path]) -> float:
    model_checker.setup_for(leakage_computer)
    with tempfile.TemporaryDirectory() as tmp_dir:
        return leakage_computer.process(model_checker.process(tmp_dir, code))


MODEL_CHECKERS = {
    "modified_cbmc": lambda unwind, **kwargs: ModifiedCBMC(unwind, **kwargs),
    "cbmc": lambda unwind, **kwargs: CBMC(unwind, **kwargs)
}


LEAKAGE_COMPUTERS = {
    "approxflow": lambda **kwargs: ApproxFlow(**kwargs),
    "relationscutter": lambda **kwargs: RelationsCutter(**kwargs)
}
