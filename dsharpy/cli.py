import logging
import time
from pathlib import Path

import click

from dsharpy.util import has_modified_cbmc, has_relationscutter, process


@click.command(name="dsharpy", help="""Using a modified CBMC and bit dependency graphs to calculate leakage

For conversion:
Private input can be obtained with undefined functions (in C/C++) or CProver functions,
see the tests in the "test/test_dsharpy.py" file.
Output via variables that start with `__out` (e.g. `__out`, `__out2`) and belong to the main function.
The main functions have to end with `END;`.
Outputs the resulting leakage.
""")
@click.argument('file', type=click.Path(exists=True, allow_dash=True, dir_okay=False))
@click.option("-v", "--verbose", type=bool, default=False)
@click.option('--unwind', type=int, default=0)
@click.option("--b16", type=bool, default=False, help="assume 16 bit integers", is_flag=True)
def cli(file, verbose: bool, unwind, b16):
    logging.basicConfig(level=logging.INFO if verbose else logging.WARNING)
    start_time = time.time()
    assert has_modified_cbmc()
    assert has_relationscutter()
    leakage = process(Path(file), unwind, )
    print(f" {time.time() - start_time:3.3f} seconds")
    print("=======================")
    print(f"Leakage: {leakage}")


if __name__ == '__main__':
    cli()
