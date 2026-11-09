# Graph Isomorphism in Quasipolynomial Time, in Lean

This repository is a Lean 4 formalization of the main results, Theorem 1.1 and Corollary 1.2, of

> MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
> *Deterministic n<sup>O(log n)</sup> Graph Isomorphism Algorithm via Inherited Decompositions*,
> [arXiv:2611.01399](https://arxiv.org/abs/2611.01399) (2026).

Theorem 1.1 says that a deterministic algorithm decides isomorphism of graphs with n vertices and
maximum degree d in time n<sup>O(log d)</sup>. Corollary 1.2 is the case of all graphs: since
d < n, graph isomorphism is decided in time n<sup>O(log n)</sup>. The Lean proof covers the whole
algorithm. It writes the algorithm as one program for a simple machine, and it proves that the
program gives correct answers within the time bound.

## The statements

Each theorem is stated in a challenge file and proved in a solution file.

```lean
-- Theorem 1.1: ChallengeDegree.lean, SolutionDegree.lean
theorem GI.graphIsomorphismInDegreeTime :
    GI.Statement.GraphIsomorphismInDegreeTime

-- Corollary 1.2: Challenge.lean, Solution.lean
theorem GI.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime
```

Three short files define them. A reader must check only these files to know what is claimed.

* [`Workspace/Statement/Machine.lean`](Workspace/Statement/Machine.lean) defines the machine. It
  is a log-cost RAM with procedure calls. Every operation costs one plus the number of binary
  digits of each number it reads or writes.
* [`Workspace/Statement/Main.lean`](Workspace/Statement/Main.lean) defines the claim for all
  graphs. There are one program `p` and one constant `C` with the following property. For every
  `n` and all graphs `G` and `H` on `n` vertices, the run of `p` on the adjacency matrices of `G`
  and `H` finishes with a correct output, at a cost of at most `exp (C * (log (n + 2)) ^ 2)`. A
  correct output says whether `G` and `H` are isomorphic. If they are, it also gives one
  isomorphism and generators of the automorphism group of `G`.
* [`Workspace/Statement/Degree.lean`](Workspace/Statement/Degree.lean) defines the claim for
  graphs of maximum degree `d`. The input and the correct output are the same. The cost is at most
  `exp (C * log (n + 2) * log (d + 2))` for every `d` such that every vertex of `G` and of `H` has
  at most `d` neighbours. The program is not given `d`. The file also proves that this claim
  implies the claim for all graphs, by taking `d = n`.

Both proofs are complete. They use only Lean's standard axioms `propext`, `Classical.choice` and
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

`lake build` builds the library and the four challenge and solution files. One file,
`Workspace/Cited/Facts.lean`, imports CFSG's proof of the classification, about 75,000 modules.
Lean maps each imported file into memory, so on Linux systems where `vm.max_map_count` is still the
old default of 65,530, this file fails to load. Raise the limit before the build, for example with
`sudo sysctl vm.max_map_count=1048576`. This file needs about 18 GB of memory. The files that
import it see only the three statements it proves, so they load much less.

## Checking with comparator

[Comparator](https://github.com/leanprover/comparator) checks that a solution file proves exactly
the statement of a challenge file. [`comparator.json`](comparator.json) sets this up for
`Challenge.lean` and `Solution.lean`, and [`comparator-degree.json`](comparator-degree.json) for
`ChallengeDegree.lean` and `SolutionDegree.lean`. This version has not yet been checked with
comparator. Its kernel check would have to replay all of CFSG.

## Layout

All Lean files of the library are in [`Workspace/`](Workspace).

* `Statement/`: the statements of the two theorems.
* `Machine/` and `Lang/`: a small programming language, its compiler to the machine, and
  facts for proving programs correct and bounding their cost.
* `Paper/`, `Algorithm/` and the files at the top of `Workspace/`: the mathematics of the
  general procedure of the paper (Sections 3 to 7 and Appendix A), and the procedure as an
  abstract recursion.
* `Impl/`: the general procedure as programs of the language, with proofs of their output and
  cost.
* `Degree/`: the proof of Theorem 1.1. It has the recursion for groups whose composition factors
  embed in the symmetric group on d points (Section 8), the structure of the primitive groups in
  this class, the recognition of Johnson actions, and the reduction from graphs to strings
  (Section 9).
* `Proved/`: polynomial-time algorithms that the paper cites. Among them are Schreier–Sims,
  normal closures, Hermite and Smith normal forms, and the vector stabilizer of Luks and
  Miyazaki.
* `Cited/`: the statements of the results that the paper cites. `Cited/Facts.lean` proves the
  three that rest on the classification.
* `Assembly/`: the final proof of Corollary 1.2, which puts the parts together.

## License

The library is under the Apache License 2.0 ([`LICENSE`](LICENSE)). Eight files are adapted from
[AxiomMath/CFSG](https://github.com/AxiomMath/CFSG), also under the Apache License 2.0.
[`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt) lists them.

[`formalization.yaml`](formalization.yaml) describes the project in the format of
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml).
