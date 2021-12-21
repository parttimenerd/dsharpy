import logging
import time
from pathlib import Path

import click

from dsharpy.tools import MODEL_CHECKERS, LEAKAGE_COMPUTERS, process


@click.command(name="dsharpy", help="""
Front end for different model checkers and associated leakage computations. 

Preprocesses c code to make it easier to write example programs for information flow.
It does add
- `#include <assert.h>` to use asserts
- `INPUT(type)` to get a random (and therefore input) value of the specified type
- `LEAK(expr)` that assigns the passed expression to a new output variable, the last leak also adds an assert
  to force the model checker to produce a SAT formula
""")
@click.argument('file', type=click.Path(exists=True, allow_dash=True, dir_okay=False))
@click.option("-m", 'model_checker', type=click.Choice(list(MODEL_CHECKERS.keys())), default="modified_cbmc")
@click.option("-l", 'leakage_computer', type=click.Choice(list(LEAKAGE_COMPUTERS.keys())), default="approxflow")
@click.option("-v", "--verbose", type=bool, default=False)
@click.option('--unwind', type=int, default=2)
@click.option("--b16", type=bool, default=False, help="assume 16 bit integers", is_flag=True)
def cli(file, model_checker, leakage_computer, verbose: bool, unwind, b16):
    logging.basicConfig(level=logging.INFO if verbose else logging.WARNING)
    start_time = time.time()
    mc = MODEL_CHECKERS[model_checker](unwind, bit_width=16 if b16 else 32)
    lc = LEAKAGE_COMPUTERS[leakage_computer]()
    leakage = process(mc, lc, Path(file))
    print(f" {time.time() - start_time:3.3f} seconds")
    print("=======================")
    print(f"Leakage: {leakage}")


if __name__ == '__main__':
    cli()
