Small tool that connects a modified [https://github.com/parttimenerd/cbmc/blob/information_flow](CBMC)
with the [https://github.com/parttimenerd/relationscutter](relationscutter) tool.

It only does a bit of preprocessing and is used for testing CBMC (both the modified and the unmodified version)
and leak computation tools like a reimplementation of ApproxFlow and relationscutter.

Usage
------------

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