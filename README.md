Small tool that connects a modified [https://github.com/parttimenerd/cbmc/blob/information_flow](CBMC)
with the [https://github.com/parttimenerd/relationscutter](relationscutter) tool.

It only does a bit of preprocessing and is used for testing CBMC (both the modified and the unmodified version)
and leak computation tools like a reimplementation of ApproxFlow and relationscutter.

Usage
------------

Compilation of the required tools via `./update.sh`
(assuming that `bison ccache cmake curl flex g++ g++-multilib gcc gcc-multilib git jq libboost-program-options-dev libc6-dev libgmp-dev libxml2-utils make ninja-build patch unzip wget zlib1g-dev python3 python3-pip` is installed).
Run `sudo tools/install_approxmc` if you have any problems with ApproxMC:
It compiles and installs a version of [ApproxMC](https://github.com/meelgroup/approxmc/) and related tools,
takes fairly long.


Installation via https://python-poetry.org

```sh

    poetry install

    # if update.sh has been called (installing the custom CBMC)
    poetry run dsharpy test.cpp --unwind 32 --lc relationscutter --mc modified_cbmc
```

Format of programs
------------------
The preprocessors adds the following:

- `#include <assert.h>` to use asserts
- `INPUT(type)` to get a random (and therefore input) value of the specified type
- `LEAK(expr)` that assigns the passed expression to a new output variable, the last leak also adds an assert
  to force the model checker to produce a SAT formula

The most basic program is given in the following as an example (more in the `tests/test_tools.py` file):

```cpp
    void main()
    {
      LEAK(INPUT(char));
    }
```

License
-------
MIT