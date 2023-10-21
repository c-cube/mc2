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

## Short Summary

MC² is a [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories).
SMT solvers are automatic tools that try to assess whether a given logic
formula is *satisfiable* (admits a model, an interpretation that makes it true)
or *unsatisfiable* (no interpretation can make it true; it is absurd, and its
negation is a theorem).
Prominent solvers include [Z3](https://github.com/Z3Prover/z3),
[cvc5](https://cvc5.github.io/), [Yices 2](https://github.com/SRI-CSL/yices2/),
and others; all of them follow the **CDCL(T)** paradigm.
Most of these solvers are implemented in C or C++.

In contract, MC² is based on the **mcSAT** calculus
(see
[[fmcad'13]](https://leodemoura.github.io/files/fmcad2013.pdf)
and
[[vmcai'13]](http://leodemoura.github.io/files/mcsat.pdf)).
mcSAT is fundamentally different from CDCL(T);
it is a so-called _natural SMT_ calculus where the boolean reasoning of CDCL is
extended so as to be able to assign values to non-boolean variables (such as
linear arithmetic variables, for example).
As a calculus it can be considered stronger, in some sense, because it can have
shorter proofs by virtue of being allowed to introduce new terms during the proof
search.
On the other hand, mcSAT is not as well known or battle tested as CDCL(T).
MC² started as an experiment to try and reproduce some results from vmcai'13.


## COPYRIGHT

This program is distributed under the Apache Software License version
2.0. See the enclosed file `LICENSE`.
