/-
The main theorem as a statement. This file, `Workspace.Statement.Main` and
`Workspace.Statement.Machine` are the trusted statement: a reader must check all three to know
what is claimed.

The claim is Theorem 1.1 of the paper (Hajiaghayi and JafariRaviz, "Deterministic
`n^{O(log n)}` Graph Isomorphism Algorithm via Inherited Decompositions"). The claim of
`Workspace.Statement.Main` is its Corollary 1.2. There is a deterministic algorithm that, given
two graphs on `n` vertices in which every vertex has at most `d` neighbours, decides whether they
are isomorphic in time `n ^ O(log (d + 2))`. If they are, it also returns one isomorphism and
generators for the full automorphism group of the first graph. The algorithm is not given `d`. It
is a program for the machine of `Workspace.Statement.Machine`, and time is the cost of its run.
-/
module

public import Workspace.Statement.Main

@[expose] public section

namespace GI.Statement

open GI.Machine

variable {n : ℕ}

/-- Every vertex of `G` has at most `d` neighbours. -/
def DegreeAtMost (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ d

/-- Every graph on `n` vertices has degree at most `n`. -/
theorem degreeAtMost_self (G : SimpleGraph (Fin n)) : DegreeAtMost G n := fun v => by
  simpa using Set.ncard_le_card (G.neighborSet v)

/-- **Theorem 1.1 of the paper, as a statement.** There are one program `p` and one constant
`C` such that the following holds for all `n` and `d`, and all graphs `G` and `H` on `Fin n` in
which every vertex has at most `d` neighbours. The run of `p` on the memory holding `G` and `H`
finishes with a correct output, at a cost of at most `exp (C * log (n + 2) * log (d + 2))`. This
bound equals `(n + 2) ^ (C * log (d + 2))`, so it is `n ^ O(log (d + 2))`.

The memory holds only `G` and `H`, so the program is not told `d`. The input layout and the
correct output are those of `GI.Statement.GraphIsomorphismInQuasipolynomialTime`. -/
def GraphIsomorphismInDegreeTime : Prop :=
  ∃ p : Program, ∃ C : ℝ, ∀ (n d : ℕ) (G H : SimpleGraph (Fin n)) (mem : ℕ → ℕ),
    InputLayout G H mem → DegreeAtMost G d → DegreeAtMost H d →
      ∃ fuel mem' r cost, run p mem fuel = some (mem', r, cost) ∧
        CorrectOutput G H mem' r ∧
        (cost : ℝ) ≤ Real.exp (C * Real.log (n + 2) * Real.log (d + 2))

/-- The degree statement implies the general one: take `d = n`. This is a check of the statement. -/
theorem quasipolynomialTime_of_degreeTime (h : GraphIsomorphismInDegreeTime) :
    GraphIsomorphismInQuasipolynomialTime := by
  obtain ⟨p, C, hp⟩ := h
  refine ⟨p, C, fun n G H mem hmem => ?_⟩
  obtain ⟨fuel, mem', r, cost, hrun, hout, hcost⟩ :=
    hp n n G H mem hmem (degreeAtMost_self G) (degreeAtMost_self H)
  refine ⟨fuel, mem', r, cost, hrun, hout, hcost.trans_eq ?_⟩
  rw [pow_two, mul_assoc]

end GI.Statement
