/-
The main theorem for Turing machines, as a statement. This file is the trusted statement: a reader
must check it to know what is claimed. Everything else in the project is proof, checked by Lean.
The file imports only Mathlib.

The claim is Theorem 1.1 of the paper (Hajiaghayi and JafariRaviz, "Deterministic `n^{O(log n)}`
Graph Isomorphism Algorithm via Inherited Decompositions") for multitape Turing machines. The
machine is Mathlib's `Turing.FinTM2`: finitely many stacks, a finite set of labels and a finite
internal state. Its input stack and its output stack hold bits. Time is the number of steps of
`Turing.FinTM2.step`. Each step runs the statement of one label, which does a bounded number of
pushes and pops, so up to a constant factor this counts the basic stack operations.

The input is the adjacency matrix of `G` followed by that of `H`, row by row, so it has `2 * n * n`
bits and determines `n`. The output says whether the graphs are isomorphic. If they are, it also
gives one isomorphism and a list of generators of the automorphism group of `G`.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Nat.Digits.Defs

@[expose] public section

namespace GI.Statement

variable {n : ℕ}

/-- The automorphism group of a graph on `Fin n`, as a group of permutations of the vertices:
the permutations `σ` such that `σ u` and `σ v` are adjacent exactly when `u` and `v` are.
These are exactly the graph isomorphisms from `G` to itself. -/
def autGroup (G : SimpleGraph (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v}
  mul_mem' {σ τ} hσ hτ u v := by
    simp only [Set.mem_ofPred_eq] at hσ hτ
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hτ]
  one_mem' u v := Iff.rfl
  inv_mem' {σ} hσ u v := by
    simp only [Set.mem_ofPred_eq] at hσ
    rw [← hσ]
    simp

/-- Every vertex of `G` has at most `d` neighbours. -/
def DegreeAtMost (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ d

/-- Every graph on `n` vertices has degree at most `n`. -/
theorem degreeAtMost_self (G : SimpleGraph (Fin n)) : DegreeAtMost G n := fun v => by
  simpa using Set.ncard_le_card (G.neighborSet v)

/-- A number `k` in binary: for each binary digit `d` of `k`, lowest first, the two bits `true`
and `d = 1`, and then `false`. A reader who stops at the first pair that starts with `false` gets
`k` back, so no such code is a prefix of another. -/
def natBits (k : ℕ) : List Bool :=
  (Nat.digits 2 k).flatMap (fun d => [true, decide (d = 1)]) ++ [false]

open Classical in
/-- The adjacency matrix of `G`, row by row: bit `n * i + j` is `true` exactly when `i` and `j`
are adjacent. -/
noncomputable def adjBits (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide (G.Adj i j)

/-- The input: the adjacency matrix of `G` and then that of `H`. It has `2 * n * n` bits. -/
noncomputable def inputBits (G H : SimpleGraph (Fin n)) : List Bool :=
  adjBits G ++ adjBits H

/-- The values `f 0, …, f (n - 1)` of a map on `Fin n`, each written with `natBits`. -/
def mapBits (f : Fin n → Fin n) : List Bool :=
  (List.finRange n).flatMap fun i => natBits (f i)

/-- A possible answer for the graphs `G` and `H`: `none` says that they are not isomorphic, and
`some (σ, gens)` gives an isomorphism `σ` from `G` to `H` and a list `gens` of permutations of
the vertices. -/
abbrev Answer (G H : SimpleGraph (Fin n)) : Type :=
  Option ((G ≃g H) × List (Equiv.Perm (Fin n)))

/-- An answer is correct if it says "not isomorphic" only when `G` and `H` are not isomorphic,
and if the permutations it lists generate the automorphism group of `G`. An answer of the form
`some (σ, gens)` is always right about isomorphism, since `σ` is an isomorphism. Every pair of
graphs has a correct answer. -/
def IsCorrectAnswer (G H : SimpleGraph (Fin n)) : Answer G H → Prop
  | none => IsEmpty (G ≃g H)
  | some (_, gens) => Subgroup.closure {g | g ∈ gens} = autGroup G

/-- The output for an answer. `none` is the single bit `false`. `some (σ, gens)` is `true`, then
the values of `σ`, then each generator as `true` followed by its values, and then `false`. Since
`n` is known from the input, the output determines the answer. -/
def answerBits {G H : SimpleGraph (Fin n)} : Answer G H → List Bool
  | none => [false]
  | some (σ, gens) =>
    true :: mapBits (fun i => σ i) ++ (gens.flatMap fun g => true :: mapBits (fun i => g i)) ++
      [false]

/-- **Theorem 1.1 of the paper, for Turing machines.** There are one Turing machine `M`, with
bits as its input and output alphabets, and one constant `C`, such that the following holds for
all `n` and `d` and all graphs `G` and `H` on `Fin n` in which every vertex has at most `d`
neighbours. Started on the input for `G` and `H`, the machine halts with the output of a correct
answer within `exp (C * log (n + 2) * log (d + 2))` steps. This bound is `n ^ O(log (d + 2))`.

Halting means the configuration `Turing.haltList`: no label is left to run, the internal state is
the initial one, the output stack holds exactly the output, and every other stack is empty. The
machine is deterministic, so it gives the same output on every run. The input holds only `G` and
`H`, so the machine is not told `d`. -/
def TuringGraphIsomorphismInDegreeTime : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℝ, ∀ (n d : ℕ) (G H : SimpleGraph (Fin n)),
    DegreeAtMost G d → DegreeAtMost H d →
      ∃ a : Answer G H, IsCorrectAnswer G H a ∧
        Nonempty (Turing.TM2OutputsInTime M.tm ((inputBits G H).map M.inputAlphabet.symm)
          (some ((answerBits a).map M.outputAlphabet.symm))
          ⌊Real.exp (C * Real.log (n + 2) * Real.log (d + 2))⌋₊)

/-- **Corollary 1.2 of the paper, for Turing machines.** The same as
`GI.Statement.TuringGraphIsomorphismInDegreeTime` for all graphs, with the bound
`exp (C * (log (n + 2)) ^ 2)`, which is `n ^ O(log n)`. -/
def TuringGraphIsomorphismInQuasipolynomialTime : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℝ, ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      ∃ a : Answer G H, IsCorrectAnswer G H a ∧
        Nonempty (Turing.TM2OutputsInTime M.tm ((inputBits G H).map M.inputAlphabet.symm)
          (some ((answerBits a).map M.outputAlphabet.symm))
          ⌊Real.exp (C * Real.log (n + 2) ^ 2)⌋₊)

/-- The degree statement implies the general one: take `d = n`. This is a check of the
statement. -/
theorem turingQuasipolynomialTime_of_degreeTime (h : TuringGraphIsomorphismInDegreeTime) :
    TuringGraphIsomorphismInQuasipolynomialTime := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨M, C, fun n G H => ?_⟩
  obtain ⟨a, ha, hrun⟩ := hM n n G H (degreeAtMost_self G) (degreeAtMost_self H)
  refine ⟨a, ha, ?_⟩
  rwa [pow_two, ← mul_assoc]

end GI.Statement
