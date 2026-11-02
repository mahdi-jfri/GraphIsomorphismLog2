import Workspace.CoherentValencies
import Workspace.RegularMatrixIndependent

namespace GI.PairRefinement

variable {n : ℕ}

def NontrivialOffDiagonal (c : Coloring n) (side : Bool) : Prop :=
  ∃ a b x y : Fin n, a ≠ b ∧ x ≠ y ∧ c (side, a, b) ≠ c (side, x, y)

theorem exists_other_offDiagonal_color (c : Coloring n) (side : Bool)
    (hn : NontrivialOffDiagonal c side) (k : Color n) :
    ∃ a b : Fin n, a ≠ b ∧ c (side, a, b) ≠ k := by
  obtain ⟨a, b, x, y, hab, hxy, hne⟩ := hn
  by_cases h : c (side, a, b) = k
  · exact ⟨x, y, hxy, fun he => hne (h.trans he.symm)⟩
  · exact ⟨a, b, hab, h⟩

/-- A monochromatic off-diagonal clique in a nontrivial homogeneous
coherent configuration has at most half of the actual vertices. -/
theorem coherent_clique_half (c : Coloring n) (hc : Coherent c) (side : Bool)
    (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    (S : Finset (Fin n)) (k : Color n)
    (clique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c (side, x, y) = k) :
    2 * S.card ≤ n := by
  obtain ⟨a, b, hab, hne⟩ := exists_other_offDiagonal_color c side hn k
  obtain ⟨d, hd, _, rows, columns⟩ := colorMatrix_regular c hc side hh a b hab
  have h := Semiregular.regular_independent_half
    (colorMatrix c side (c (side, a, b))) d rows columns hd S ?_
  · simpa using h
  · intro x hx y hy
    change decide (c (side, x, y) = c (side, a, b)) = false
    apply decide_eq_false_iff_not.mpr
    intro heq
    by_cases hxy : x = y
    · subst y
      exact offDiagonal_loop_ne c hc side a b x hab heq
    · exact hne (heq.symm.trans (clique x hx y hy hxy))

theorem run_nontrivial (c : Coloring n) (side : Bool) (hn : NontrivialOffDiagonal c side) :
    NontrivialOffDiagonal (run c) side := by
  obtain ⟨a, b, x, y, hab, hxy, hne⟩ := hn
  exact ⟨a, b, x, y, hab, hxy, fun he => hne (run_refines c he)⟩

theorem refined_clique_half (c : Coloring n) (side : Bool)
    (hn : NontrivialOffDiagonal c side)
    (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPretransitive H (Fin n)]
    (preserves : ∀ h : H, Transports c side side h.val)
    (S : Finset (Fin n)) (k : Color n)
    (clique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → run c (side, x, y) = k) :
    2 * S.card ≤ n :=
  coherent_clique_half (run c) (run_coherent c) side
    (run_homogeneous c side H preserves) (run_nontrivial c side hn) S k clique

end GI.PairRefinement
