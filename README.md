# Graph Isomorphism in Quasipolynomial Time, in Lean

This repository is a Lean 4 formalization of the main theorem of

> MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
> *Deterministic n<sup>O(log n)</sup> Graph Isomorphism Algorithm via Inherited Decompositions*.

The theorem says that a deterministic algorithm decides graph isomorphism in time
n<sup>O(log n)</sup>. The Lean proof covers the whole algorithm. It writes the algorithm as one
program for a simple machine, and it proves that the program gives correct answers within the
time bound.

## The statement

The main theorem is `main_theorem` in [`Challenge.lean`](Challenge.lean):

```lean
theorem main_theorem : GI.Statement.GraphIsomorphismInQuasipolynomialTime
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

The proof of the main theorem is `GI.graphIsomorphismInQuasipolynomialTime` in
[`Workspace/Assembly/Main.lean`](Workspace/Assembly/Main.lean).

## What the proof assumes

Besides Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`, the proof uses ten
results from the literature as axioms. Each of them relies on the classification of finite
simple groups. [`AXIOMS.md`](AXIOMS.md) lists them with their sources.

## Building

The project uses Lean `v4.30.0-rc2` and mathlib at commit `2f9133a`. With
[elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get   # download the compiled mathlib
lake build           # build the formalization and Solution.lean
```

To print the axioms that the main theorem uses:

```sh
printf 'import Solution\n#print axioms main_theorem\n' | lake env lean --stdin
```

## Checking with comparator

[Comparator](https://github.com/leanprover/comparator) checks that a solution file proves exactly
the statement of a challenge file, and that it uses only allowed axioms.
[`comparator.json`](comparator.json) sets this up.

* [`Challenge.lean`](Challenge.lean) states `main_theorem` with `sorry`. Besides mathlib, it
  imports only the statement and the ten axioms of [`AXIOMS.md`](AXIOMS.md).
* [`Solution.lean`](Solution.lean) proves `main_theorem`.
* The allowed axioms are Lean's three standard axioms and the ten axioms. Comparator checks that
  the solution uses these axioms with the same statements as the challenge.

Comparator needs [`landrun`](https://github.com/Zouuup/landrun) and
[`lean4export`](https://github.com/leanprover/lean4export) on `PATH`. For the Lean version of
this project, build comparator and lean4export from their `v4.30.0-rc2` tags, and landrun from
its commit `5ed4a3d` (version 0.1.15). Later versions of landrun need a later comparator. Then
run, from the repository root:

```sh
lake env /path/to/comparator comparator.json
```

With these versions, comparator accepts the solution. The kernel check takes about half an hour.

## Layout

All Lean files are in [`Workspace/`](Workspace).

* `Statement/`: the statement of the main theorem.
* `Machine/` and `Lang/`: a small programming language, its compiler to the machine, and
  facts for proving programs correct and bounding their cost.
* `Paper/`, `Algorithm/` and the files at the top of `Workspace/`: the mathematics of the
  paper, and its algorithm as an abstract recursion.
* `Impl/`: the algorithm as programs of the language, with proofs of their output and cost.
* `Proved/`: polynomial-time algorithms that the paper cites and that are proved here. Among
  them are Schreier–Sims, normal closures, Hermite and Smith normal forms, and the vector
  stabilizer of Luks and Miyazaki.
* `Cited/` and `Axioms/`: the statements of the cited results, and the ten axioms.
* `Assembly/`: the final proof, which puts the parts together.

## Third-party code

Eight files are adapted from [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG) and are under
the Apache License 2.0. [`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt) lists them.
