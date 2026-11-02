import Workspace.SocleSimpleAlternative
import Workspace.PrimitiveSubdirectDegree
import Workspace.PrimitiveTwoNormalDegree

namespace GI.BudgetInduction

open RadicalSocle PrimitiveStructure

/-- Combining the actual proper-projection, subdirect, and two-normal
cases leaves only a simple socle or a quadratic bound on its order.
The unsupported premise refers to the previously defined physical
valuation/Cartesian/Johnson reductions, not to a classification claim. -/
theorem unsupported_socle_simple_or_order_le_degree_sq {n : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [Nontrivial (Fin n)]
    [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥)
    (a : Fin n) (unsupported : ¬ PrimitiveReductionAlternative A₀ H) :
    IsSimpleGroup (socle H) ∨ Nat.card (socle H) ≤ n ^ 2 := by
  classical
  haveI : Nontrivial H := by
    obtain ⟨b, hb⟩ := exists_ne a
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a b
    refine ⟨⟨g, 1, ?_⟩⟩
    intro he
    rw [he, one_smul] at hg
    exact hb hg.symm
  obtain ⟨N, hN, _⟩ := exists_minimal_normal_le (⊤ : Subgroup H) top_ne_bot
  letI : N.Normal := hN.1
  by_cases hpair : ∃ M : Subgroup H, MinimalNormal M ∧ M ≠ N
  · obtain ⟨M, hM, hne⟩ := hpair
    right
    have he := two_minimal_socle_card_eq_degree_sq hM hN hne a
    exact le_of_eq (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using he)
  · have hsoc : socle H = N := by
      apply le_antisymm
      · apply socle_le_normal
        intro M hM
        exact le_of_eq (not_ne_iff.mp (fun hne => hpair ⟨M, hM, hne⟩))
      · exact minimalNormal_le_socle hN
    by_cases hcount : 2 ≤ Nat.card (MinimalNormals N)
    · right
      rw [hsoc]
      exact unsupported_minimalNormal_order_le_degree_sq H radicalFree N hN a hcount unsupported
    · left
      rw [hsoc]
      letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
      exact simple_of_socle_eq_top_count_le_one (minimalNormal_socle_eq_top hN) (by omega)

/-- The simple branch includes the actual faithful conjugation map and
the inner subgroup of its image. The other branch bounds actual order. -/
theorem unsupported_almost_simple_or_socle_order_le_degree_sq {n : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [Nontrivial (Fin n)]
    [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥)
    (a : Fin n) (unsupported : ¬ PrimitiveReductionAlternative A₀ H) :
    (IsSimpleGroup (socle H) ∧ Function.Injective (socleConjugation (G := H)) ∧
      GI.SocleOuter.innerAut (socle H) ≤ (socleConjugation (G := H)).range) ∨
      Nat.card (socle H) ≤ n ^ 2 := by
  rcases unsupported_socle_simple_or_order_le_degree_sq H radicalFree a unsupported with hs | hb
  · exact Or.inl (socle_almost_simple_embedding radicalFree hs)
  · exact Or.inr hb

end GI.BudgetInduction
