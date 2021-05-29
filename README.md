# MC2  [![build](https://github.com/c-cube/mc2/actions/workflows/main.yml/badge.svg)](https://github.com/c-cube/mc2/actions/workflows/main.yml)

MC² ("Model Constructing Modular Contraption") is a modular SMT solver
in OCaml, based on the MCSat calculus.

It implements most of the techniques described in de Moura and Jovanović
(VMCAI 13), in around 7 thousands lines of code (not including dependencies).
EUF is supported via congruence lemmas; LRA is based on a conflict-driven
Fourier-Motzkin solver. Boolean formulas are turned into clauses during preprocessing,
using the Tseitin encoding; the core solver handles clauses like a regular SAT
solver, as the code was originally derived from
msat (github.com/Gbury/mSAT), itself derived from Alt-Ergo Zero.
However most of the code was modified or rewritten by Simon Cruanes while
working at Veridis at Loria, Nancy, France; and later in his own free time.


## Documentation

https://c-cube.github.io/mc2/

## COPYRIGHT

This program is distributed under the Apache Software License version
2.0. See the enclosed file `LICENSE`.
