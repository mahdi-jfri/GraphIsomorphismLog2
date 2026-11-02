/-
The main theorem as a statement. This file and `Workspace.Statement.Machine` are the trusted
statement: a reader must check both to know what is claimed. Everything else in the project is
proof, checked by Lean.

The claim is Theorem 1.1 of the paper (Hajiaghayi and JafariRaviz, "Deterministic `n^{O(log n)}`
Graph Isomorphism Algorithm via Inherited Decompositions"). There is a deterministic algorithm
that, given two graphs on `n` vertices, decides whether they are isomorphic in time
`exp (O ((log (n + 2)) ^ 2))`. If they are, it also returns one isomorphism and generators for
the full automorphism group of the first graph. Here an algorithm is a program for the machine
of `Workspace.Statement.Machine`, and time is the cost of its run.
-/
import Workspace.Statement.Machine
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GI.Statement

open GI.Machine

variable {n : ℕ}

/-- The automorphism group of a graph on `Fin n`, as a group of permutations of the vertices:
the permutations `σ` such that `σ u` and `σ v` are adjacent exactly when `u` and `v` are.
These are exactly the graph isomorphisms from `G` to itself. -/
def autGroup (G : SimpleGraph (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v}
  mul_mem' {σ τ} hσ hτ u v := by
    simp only [Set.mem_setOf_eq] at hσ hτ
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hτ]
  one_mem' u v := Iff.rfl
  inv_mem' {σ} hσ u v := by
    simp only [Set.mem_setOf_eq] at hσ
    rw [← hσ]
    simp

open Classical in
/-- The input: two graphs `G` and `H` on `Fin n`, laid out in memory as their adjacency
matrices. Cell 0 holds `n`. Cell `1 + n * i + j` holds 1 if `i` and `j` are adjacent in `G`
and 0 otherwise, and cell `1 + n * n + n * i + j` does the same for `H`. Every later cell holds
0. These rules fix every cell (`GI.Statement.inputLayout_unique`), and such a memory exists
(`GI.Statement.inputLayout_exists`). -/
structure InputLayout (G H : SimpleGraph (Fin n)) (mem : ℕ → ℕ) : Prop where
  size : mem 0 = n
  left : ∀ i j : Fin n, mem (1 + n * i + j) = if G.Adj i j then 1 else 0
  right : ∀ i j : Fin n, mem (1 + n * n + n * i + j) = if H.Adj i j then 1 else 0
  rest : ∀ a, 2 * n * n < a → mem a = 0

/-- A correct output, starting at the address `r` that the program returns.
* If `G` and `H` are not isomorphic, cell `r` holds 0.
* If they are, cell `r` holds 1, and the cells after it hold:
  - an isomorphism `σ` from `G` to `H`: cell `r + 1 + i` holds `σ i`, for `i < n`;
  - the number `k` of generators, in cell `r + 1 + n`;
  - the generators `g 0, …, g (k - 1)`: cell `r + 2 + n + n * t + i` holds `g t i`.
  These generators generate the automorphism group of `G`.

Every pair of graphs has a correct output. -/
def CorrectOutput (G H : SimpleGraph (Fin n)) (mem : ℕ → ℕ) (r : ℕ) : Prop :=
  (mem r = 0 ∧ IsEmpty (G ≃g H)) ∨
  (mem r = 1 ∧ ∃ σ : G ≃g H, (∀ i : Fin n, mem (r + 1 + i) = σ i) ∧
    ∃ gens : List (Equiv.Perm (Fin n)), mem (r + 1 + n) = gens.length ∧
      (∀ (t : Fin gens.length) (i : Fin n), mem (r + 2 + n + n * t + i) = gens.get t i) ∧
      Subgroup.closure {g | g ∈ gens} = autGroup G)

/-- **Theorem 1.1 of the paper, as a statement.** There are one program `p` and one constant
`C` such that the following holds for every `n` and all graphs `G` and `H` on `Fin n`. The run
of `p` on the memory holding `G` and `H` finishes with a correct output, at a cost of at most
`exp (C * (log (n + 2)) ^ 2)`. This bound equals `(n + 2) ^ (C * log (n + 2))`, so it
is `n ^ O(log n)`.

The machine is deterministic, so all runs that finish give the same memory, return value and
cost. Hence `∃ fuel` cannot pick a cheaper run. -/
def GraphIsomorphismInQuasipolynomialTime : Prop :=
  ∃ p : Program, ∃ C : ℝ, ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (mem : ℕ → ℕ),
    InputLayout G H mem →
      ∃ fuel mem' r cost, run p mem fuel = some (mem', r, cost) ∧
        CorrectOutput G H mem' r ∧
        (cost : ℝ) ≤ Real.exp (C * Real.log (n + 2) ^ 2)

end GI.Statement
