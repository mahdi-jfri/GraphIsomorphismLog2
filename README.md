# Graph Isomorphism in Quasipolynomial Time, in Lean

This repository is a Lean 4 formalization of the main theorem, Theorem 1.1, of

> MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
> *Deterministic n<sup>O(log n)</sup> Graph Isomorphism Algorithm via Inherited Decompositions*,
> [arXiv:2611.01399v1](https://arxiv.org/abs/2611.01399v1) (2026).

The theorem says that a deterministic algorithm decides graph isomorphism in time
n<sup>O(log n)</sup>. The Lean proof covers the whole algorithm. It writes the algorithm as one
program for a simple machine, and it proves that the program gives correct answers within the
time bound.

## The statement

The main theorem is stated in [`Challenge.lean`](Challenge.lean) and proved in
[`Solution.lean`](Solution.lean):

```lean
theorem GI.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime
```

Two short files define it. A reader must check only these two files to know what is claimed.

* [`Workspace/Statement/Machine.lean`](Workspace/Statement/Machine.lean) defines the machine. It
  is a log-cost RAM with procedure calls. Every operation costs one plus the number of binary
  digits of each number it reads or writes.
* [`Workspace/Statement/Main.lean`](Workspace/Statement/Main.lean) defines the claim. There are
  one program `p` and one constant `C` with the following property. For every `n` and all graphs
  `G` and `H` on `n` vertices, the run of `p` on the adjacency matrices of `G` and `H` finishes
  with a correct output, at a cost of at most `exp (C * (log (n + 2)) ^ 2)`. A correct output
  says whether `G` and `H` are isomorphic. If they are, it also gives one isomorphism and
  generators of the automorphism group of `G`.

The proof is complete. It uses only Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Dependencies

The paper uses three results that rest on the classification of finite simple groups. They are
proved in two other formalizations, and this library depends on both.

* [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG) proves the classification of finite simple
  groups, and Schreier's conjecture for the groups on the classification list: their outer
  automorphism groups are solvable.
* [MarotiOrdersOfPrimitiveGroups](https://github.com/mahdi-jfri/MarotiOrdersOfPrimitiveGroups)
  proves Maróti's bound on the orders of primitive permutation groups (A. Maróti, *On the orders
  of primitive groups*, J. Algebra 258 (2002), Theorem 1.1). It also builds on AxiomMath/CFSG.

[`Workspace/Cited/Facts.lean`](Workspace/Cited/Facts.lean) derives the three results from these
proofs. The library also depends on [Mathlib](https://github.com/leanprover-community/mathlib4)
and [TauCeti](https://github.com/TauCetiProject/TauCeti), at the revisions that AxiomMath/CFSG uses.
[`lakefile.lean`](lakefile.lean) pins all four.

## Building

The project uses Lean `v4.35.0-rc3`. CFSG publishes its build files for Linux x86_64. To download
them, along with those of Mathlib and TauCeti, and build, run from the repository root:

```sh
ulimit -s 1048576
export RUST_MIN_STACK=1073741824 LAKE_ARTIFACT_CACHE=true
lake env true      # fetch the dependencies
LAKE_CACHE_MAX_REVS=1 bash .lake/packages/MarotiOrdersOfPrimitiveGroups/tools/lake-cache-get-fast.sh .
lake build
```

`lake build` builds the library, `Challenge.lean` and `Solution.lean`. One file,
`Workspace/Cited/Facts.lean`, imports CFSG's proof of the classification, about 75,000 modules.
Lean maps each imported file into memory, so on Linux systems where `vm.max_map_count` is still the
old default of 65,530, this file fails to load. Raise the limit before the build, for example with
`sudo sysctl vm.max_map_count=1048576`. This file needs about 18 GB of memory. The files that
import it see only the three statements it proves, so they load much less.

## Checking with comparator

[Comparator](https://github.com/leanprover/comparator) checks that a solution file proves exactly
the statement of a challenge file. [`comparator.json`](comparator.json) sets this up for
`Challenge.lean` and `Solution.lean`. This version has not yet been checked with comparator. Its
kernel check would have to replay all of CFSG.

## Layout

All Lean files of the library are in [`Workspace/`](Workspace).

* `Statement/`: the statement of the main theorem.
* `Machine/` and `Lang/`: a small programming language, its compiler to the machine, and
  facts for proving programs correct and bounding their cost.
* `Paper/`, `Algorithm/` and the files at the top of `Workspace/`: the mathematics of the
  paper, and its algorithm as an abstract recursion.
* `Impl/`: the algorithm as programs of the language, with proofs of their output and cost.
* `Proved/`: polynomial-time algorithms that the paper cites. Among them are Schreier–Sims,
  normal closures, Hermite and Smith normal forms, and the vector stabilizer of Luks and
  Miyazaki.
* `Cited/`: the statements of the results that the paper cites. `Cited/Facts.lean` proves the
  three that rest on the classification.
* `Assembly/`: the final proof, which puts the parts together.

## License

The library is under the Apache License 2.0 ([`LICENSE`](LICENSE)). Eight files are adapted from
[AxiomMath/CFSG](https://github.com/AxiomMath/CFSG), also under the Apache License 2.0.
[`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt) lists them.

[`formalization.yaml`](formalization.yaml) describes the project in the format of
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml).
