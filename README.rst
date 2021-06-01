An approximate model counter with dependencies. This is an extension of #SAT to support loop approximations in QIFC.

**TL;DR: This repo contains a python layer for the output of the modified CBMC version https://git.scc.kit.edu/gp1285/cbmc, the
initial aim was to develop an extension of #SAT, but this ran into theoretical difficulties. This repositories
can be the starting point for further research.**

This is based on ApproxMC (and the related research). It uses AMC as an oracle by default.

Work in progress (and it is unclear whether it really works).

It might still return a number that is to low.

It can analyse C/C++ and Java code using a modified CBMC as a front end. This includes heavy preprocessing.

See https://www.overleaf.com/read/smkhyhdytccr for more information on the underlying ideas and techniques.

Requirements
------------
- Linux

License
-------
MIT

Installation
------------

via https://python-poetry.org

.. code::

    poetry install

    poetry run dsharpy test.cnf

    # if update.sh has been called (installing the custom CBMC)
    poetry run dsharpy test.c

Syntax of DCNF files
--------------------
Normal CNF DIMACS Syntax:

The header is:

.. code::

  p cnf [number of variables] [number of clauses]

This is followed by the clauses that consist of integer literals starting at 1.
A negative literal is the negated positive literal. Each clause ends with 0.

Comments can be added by prefixing a line with ``c``.

The additional features are realized via comments:

- c ind [variables to count models] 0
- c dep a_1 … a_n 0 b_1 … b_m 0 [c_1 … c_k 0 [d 0 [oa 0]]]
    - tells the counter to assume that there is arbitrary relation between a_1, …, a_n and b_1, …, b_m
    - the relation (and its arguments) satisfy the constraints c_1, …, c_k
    - the maximum variability of a_1, …, a_n is d
    - oa = 1: fully over approximate (skip computing the variability of a_1, …, a_n), oa = 0: do not skip (the default)

Attention: The different ``dep`` comments might have to have pairwise disjoint left and right sides each

See for examples in ``tests/cases`` and ``tests/test_dsharpy``.


MaxCount
--------
It also contains a fork of https://github.com/dfremont/maxcount that supports approximately solving
a DCNF based MAX#SAT problem.

The only addition to prior described format is that the maximization variables can
be specified via

.. code::

  c max var_1 … var_n 0


Attention: It is only a really rough modification of the original code