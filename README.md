# Graph Isomorphism in Quasipolynomial Time, in Lean

This repository is a Lean 4 formalization of the main results, Theorem 1.1 and Corollary 1.2, of

> MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
> *Deterministic n<sup>O(log n)</sup> Graph Isomorphism Algorithm via Inherited Decompositions*,
> [arXiv:2611.01399](https://arxiv.org/abs/2611.01399) (2026).

Theorem 1.1 says that a deterministic algorithm decides isomorphism of graphs with n vertices and
maximum degree d in time n<sup>O(log d)</sup>. Corollary 1.2 is the case of all graphs: since
d < n, graph isomorphism is decided in time n<sup>O(log n)</sup>. The Lean statement is about
Mathlib's multitape Turing machines. The proof covers the whole algorithm: it builds one Turing
machine and proves that it gives correct answers within the time bound.

## The statements

[`Challenge.lean`](Challenge.lean) states the two theorems with `sorry`, and
[`Solution.lean`](Solution.lean) proves them.

```lean
-- Theorem 1.1
theorem GI.turingGraphIsomorphismInDegreeTime :
    GI.Statement.TuringGraphIsomorphismInDegreeTime

-- Corollary 1.2
theorem GI.turingGraphIsomorphismInQuasipolynomialTime :
    GI.Statement.TuringGraphIsomorphismInQuasipolynomialTime
```

One short file, [`Workspace/Statement/Turing.lean`](Workspace/Statement/Turing.lean), defines
both statements, and it imports only Mathlib. A reader must check only this file to know what is
claimed. `Challenge.lean` repeats its definitions word for word.

* The machine is Mathlib's `Turing.FinTM2`. It has finitely many stacks, a finite set of labels
  and a finite internal state. Its input stack and its output stack hold bits. Time is the
  number of steps of `Turing.FinTM2.step`.
* The input is the adjacency matrix of a graph `G` on `n` vertices, row by row, followed by that
  of a graph `H`, so it has `2 * n * n` bits.
* The output is a correct answer. It is the bit `false` if `G` and `H` are not isomorphic.
  Otherwise it is the bit `true`, one isomorphism from `G` to `H`, and a list of generators of
  the automorphism group of `G`. Each number is written in binary in a code where no code word
  is a prefix of another.
* Theorem 1.1 says that there are one machine `M` and one constant `C` with the following
  property. For all `n` and `d` and all graphs `G` and `H` on `n` vertices in which every vertex
  has at most `d` neighbours, `M` started on the input for `G` and `H` halts with a correct
  answer within `exp (C * log (n + 2) * log (d + 2))` steps. The machine is not given `d`.
* Corollary 1.2 says the same for all graphs, with the bound `exp (C * (log (n + 2)) ^ 2)`. The
  statement file proves that it follows from Theorem 1.1 by taking `d = n`.

[`Workspace/Turing/Checks/`](Workspace/Turing/Checks) proves facts about the statement: no two
answers have the same output, inputs of different graphs differ, and every pair of graphs has a
correct answer.

Both proofs are complete. They use only Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## The proof

The proof has two steps.

1. The algorithm is first written as one program for a log-cost RAM with procedure calls
   ([`Workspace/Statement/Machine.lean`](Workspace/Statement/Machine.lean)). Every operation of
   this machine costs one plus the number of binary digits of each number it reads or writes.
   [`Workspace/Statement/Degree.lean`](Workspace/Statement/Degree.lean) states Theorem 1.1 for
   this machine, and `Workspace/Degree/` proves it.
2. [`Workspace/Turing/`](Workspace/Turing) runs every program of this machine on a Turing machine
   with a polynomial slowdown. It goes through a stack machine
   ([`Workspace/Turing/SM.lean`](Workspace/Turing/SM.lean)). A polynomial of
   `exp (C * log (n + 2) * log (d + 2))` is again of that form, with a larger `C`.

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

The project uses Lean `v4.35.0`. CFSG publishes its build files for Linux x86_64. To download
them, along with those of Mathlib and TauCeti, and build, run from the repository root:

```sh
ulimit -s 1048576
export RUST_MIN_STACK=1073741824 LAKE_ARTIFACT_CACHE=true
lake env true      # fetch the dependencies
LAKE_CACHE_MAX_REVS=1 bash .lake/packages/MarotiOrdersOfPrimitiveGroups/tools/lake-cache-get-fast.sh .
lake build
```

`lake build` builds the library and the challenge and solution files. One file,
`Workspace/Cited/Facts.lean`, imports CFSG's proof of the classification, about 75,000 modules.
Lean maps each imported file into memory, so on Linux systems where `vm.max_map_count` is still the
old default of 65,530, this file fails to load. Raise the limit before the build, for example with
`sudo sysctl vm.max_map_count=1048576`. This file needs about 18 GB of memory. The files that
import it see only the three statements it proves, so they load much less.

## Checking with comparator

[Comparator](https://github.com/leanprover/comparator), which Lean `v4.35.0` includes as
`lake comparator`, checks that a solution file proves exactly the statement of a challenge file.
[`comparator.json`](comparator.json) sets this up for `Challenge.lean` and `Solution.lean`. Since
`Challenge.lean` imports only Mathlib, comparator checks that the definitions that
`Solution.lean` uses are the ones of `Challenge.lean`. This version has not yet been checked with
comparator. Its kernel check would have to replay all of CFSG.

## Layout

All Lean files of the library are in [`Workspace/`](Workspace).

* `Statement/`: `Turing.lean` states the two theorems. `Machine.lean`, `Main.lean` and
  `Degree.lean` state them for the log-cost machine, the first step of the proof.
* `Turing/`: the simulation of the log-cost machine on Turing machines (the second step of the
  proof), and in `Turing/Checks/` the checks of the statement.
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
* `Assembly/`: Corollary 1.2 for the log-cost machine, from the general procedure as one
  program. The proof of Theorem 1.1 uses it.

## License

The library is under the Apache License 2.0 ([`LICENSE`](LICENSE)). Eight files are adapted from
[AxiomMath/CFSG](https://github.com/AxiomMath/CFSG), also under the Apache License 2.0.
[`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt) lists them.

[`formalization.yaml`](formalization.yaml) describes the project in the format of
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml).
