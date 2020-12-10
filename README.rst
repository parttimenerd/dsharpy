An approximate model counter with dependencies. This is an extension of #SAT to support loop approximations in QIFC.

This is based on ApproxMC (and the related research). It uses AMC as an oracle by default.

Work in progress (and it is unclear whether it really works).

It might still return a number that is to low.

Requirements
------------
- Linux

Installation
------------

via https://python-poetry.org

.. code::

    poetry install

    poetry run dsharpy

Syntax of DCNF files
--------------------
Normal CNF DIMACS Syntax:

The header is:

.. code::

  p cnf [number of variables] [number of clauses]

This is followed by the clauses that consist of integer literals starting at 1.
A negative literal is the negated positive literal. Each clause ends with 0.

Comments can be added by prefixing a line with ``c``.

The additionial features are realized via comments:

- c ind [variables to count models] 0
- c dep a b_1 … b_n 0
    - tells the counter to assume that there is arbitrary relation between a and b_1, …, b_n
- c par a_1 b_1 a_2 b_2 …
    - asserts that the relations a_i ~> b_i don't affect each other
    - helps to improve the performance of the counter

See for examples in ``tests/cases``.


MaxCount
--------
It also contains a fork of https://github.com/dfremont/maxcount that supports approximately solving
a DCNF based MAX#SAT problem.

The only addition to prior described format is that the maximation variables can
be specified via

.. code::

  c max var_1 … var_n 0


Attention: It is only a really rough modification of the original code


TODO
----
- using the passed epsilon and delta values to compute the amc_epsilon, the amc_delta and the number of iterations
- larger test cases
