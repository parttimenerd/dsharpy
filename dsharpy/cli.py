import logging
import math
import os
import time

import click

from dsharpy.counter import Config, State
from dsharpy.formula import DCNF
from dsharpy.util import DepGenerationPolicy, CBMCOptions, random_seed, detect_file_suffix, has_modified_cbmc, \
    process_code_with_cbmc, process_code_with_jbmc


@click.command(name="dsharpy", help="""An approximate model counter with dependencies based on ApproxMC

Approximate the number of models of the passed DCNF or C/C++/Java (via modified CBMC) file.

For conversion:
Private input can be obtained with undefined functions (in C/C++) or CProver functions,
see the tests in the "test/test_dsharpy.py" file.
Output via variables that start with `__out` (e.g. `__out`, `__out2`).
The main functions have to end with `END;`.
Outputs the resulting DCNF.
""")
@click.argument('file', type=click.Path(exists=True, allow_dash=True, dir_okay=False))
@click.option("-v", "--verbose", type=bool, default=False)
@click.option("--random", default=lambda: os.urandom(100))
@click.option('-p', '--parallelism', type=int, default=-1, help="-1: use system parallelism, "
                                                                "> 0: level of parallelism, other values are unsupported")
@click.option('--amc_epsilon', type=float, default=0.2)
@click.option('--amc_delta', type=float, default=0.8)
@click.option("--epsilon", type=float, default=0.2, help="Not yet implemented")
@click.option("--delta", type=float, default=0.8, help="Not yet implemented")
@click.option("--check_xor_variability", type=int, default=10,
              help="0: don't check, > 0: Check that the added xors lead to the variables having"
              "the desired variability in the rest of the program, use the xors that are nearest to desired variability")
@click.option("--iterations", type=int, default=5, help="number of loop iterations")
@click.option("--only_convert", type=bool, default=False, help="only convert the C/C++/Java file")
@click.option('--out', type=click.File(mode='w'), default='-', help="Output file or '-' for standard out")
@click.option('--unwind', type=int, default=3, help="< 3 not allowed, last iteration used for abstraction")
@click.option('--abstract_rec', type=int, default=0, help="-1: don't use it, >= 0: with depth")
@click.option('--dep_gen_policy', type=DepGenerationPolicy, default=DepGenerationPolicy.FULL_VARS)
@click.option('--compute_max_vars', type=bool, default=False)
def cli(file, verbose: bool, random: float, parallelism, amc_epsilon, amc_delta,
        epsilon, delta, check_xor_variability, iterations, only_convert, out,
        unwind, abstract_rec, dep_gen_policy, compute_max_vars):
    logging.warning("--epsilon and --delta don't have any effect currently")
    random_seed(random)
    logging.basicConfig(level=logging.INFO if verbose else logging.WARNING)
    config = Config(parallelism=parallelism,
                    amc_epsilon=amc_epsilon,
                    amc_delta=amc_delta,
                    log_iterations=verbose,
                    epsilon=epsilon,
                    delta=delta,
                    check_xor_variability=check_xor_variability > 0,
                    max_xor_retries=check_xor_variability)
    cbmc_options = CBMCOptions(unwind=unwind, abstract_rec=abstract_rec if abstract_rec != -1 else None,
                               dep_gen_policy=dep_gen_policy, compute_max_vars=compute_max_vars,
                               verbose=verbose, counter_config=config)
    file_content = ""
    with click.open_file(file) as f:
        file_content = f.read()

    string = ""
    suffix = detect_file_suffix(file_content)
    if suffix == ".cnf":
        string = file_content
        assert not only_convert
    else:
        start_convert = time.time()
        assert has_modified_cbmc()
        if suffix in [".c", ".cpp"]:
            string = process_code_with_cbmc(file_content, options=cbmc_options)
        elif suffix == ".java":
            string = process_code_with_jbmc(file_content, options=cbmc_options)
        else:
            logging.error(f"Unsupported file type")
            exit(1)
        print(f"c converted in {time.time() - start_convert:3.3f} seconds")
    if only_convert:
        print(string, file=out)
    else:
        start_count = time.time()
        state = State(DCNF.load_string(string), config=config)
        ret = state.compute_loop(iterations)
        if ret >= 0:
            print(f"c count {ret}")
            print(f"c bit count {math.log2(ret):3.3f}")
        else:
            print(f"c unsatisfiable")
        print(f"c counted in {time.time() - start_count:3.3f} seconds")


if __name__ == '__main__':
    cli()
