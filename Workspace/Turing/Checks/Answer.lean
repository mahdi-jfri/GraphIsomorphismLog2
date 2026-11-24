/-
Existence of a correct answer in `Workspace.Statement.Turing`.

We prove that every pair of graphs `G` and `H` on `Fin n` has an `a : Answer G H` satisfying
`IsCorrectAnswer G H a`. When `G` and `H` are not isomorphic, `none` is correct. When they are
isomorphic, any isomorphism together with the list of all elements of `autGroup G` is correct.
-/
module

public import Workspace.Statement.Turing
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace GI.Turing

open GI.Statement

/-- Every pair of graphs on `Fin n` has a correct answer. -/
theorem exists_correctAnswer {n : ℕ} (G H : SimpleGraph (Fin n)) :
    ∃ a : Answer G H, IsCorrectAnswer G H a := by
  classical
  by_cases h : Nonempty (G ≃g H)
  · obtain ⟨σ⟩ := h
    refine ⟨some (σ, (Finset.univ.filter (· ∈ autGroup G)).toList), ?_⟩
    show Subgroup.closure {g | g ∈ (Finset.univ.filter (· ∈ autGroup G)).toList} = autGroup G
    have hset :
        {g : Equiv.Perm (Fin n) | g ∈ (Finset.univ.filter (· ∈ autGroup G)).toList} =
          (autGroup G : Set (Equiv.Perm (Fin n))) := by
      ext g
      simp
    rw [hset, Subgroup.closure_eq]
  · exact ⟨none, not_nonempty_iff.mp h⟩

end GI.Turing
