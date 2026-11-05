module

public import Workspace.BudgetInductionAffine

@[expose] public section

/-! An unconditional logarithmic alternating-section bound for the concrete
affine group. This is a weaker numerical bound than paper A.15: it does not
prove the sharp threshold `max (8) (2 + log₂ n)` or classify primitive groups. -/

namespace GI.A15Work

open MatrixValuation

variable {F : Type*} [Field F] [Fintype F] {d k : ℕ}

/-- An actual alternating section of an affine subgroup has logarithmic
degree. No transitivity, simplicity, or primitive classification is supplied. -/
theorem affine_alternating_section_bound (H : Subgroup (AffineGroup F d))
    (hk : 64 ≤ k) (hdvd : Nat.card (alternatingGroup (Fin k)) ∣ Nat.card H) :
    (k : ℝ) ≤ (12 / Real.log 2) * Real.log ((Fintype.card F : ℝ) ^ d) := by
  obtain ⟨p, hp, hb⟩ := affine_subgroup_uniform_bound F d H
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  have hm := primeValuation_mono (p := p) (Nat.ne_of_gt (Nat.card_pos (α := H))) hdvd
  have hw := alternating_weight_valuation hp hk
  have hle : k ≤ 6 * padicValNat p (Nat.card H) :=
    hw.trans (Nat.mul_le_mul_left 6 hm)
  exact (show (k : ℝ) ≤ 6 * (padicValNat p (Nat.card H) : ℝ) by
    exact_mod_cast hle).trans hb

theorem affine_alternating_quotient_bound (H : Subgroup (AffineGroup F d))
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q) :
    (k : ℝ) ≤ max 63 ((12 / Real.log 2) * Real.log ((Fintype.card F : ℝ) ^ d)) := by
  by_cases hk : 64 ≤ k
  · exact (affine_alternating_section_bound H hk
      (Subgroup.card_dvd_of_surjective (f := q) hq)).trans (le_max_right _ _)
  · exact (show (k : ℝ) ≤ 63 by exact_mod_cast (show k ≤ 63 by omega)).trans
      (le_max_left _ _)

/-- The same exclusion applies to arbitrary subgroup sections of an actual
affine image, including the constructed faithful natural permutation image. -/
theorem affine_image_alternating_quotient_bound {V : Type*} [Fintype V]
    (p : AffineGroup F d →* Equiv.Perm V)
    (H : Subgroup (Equiv.Perm V)) (hH : H ≤ p.range)
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q) :
    (k : ℝ) ≤ max 63 ((12 / Real.log 2) * Real.log ((Fintype.card F : ℝ) ^ d)) := by
  by_cases hk : 64 ≤ k
  · have hdvd := (Subgroup.card_dvd_of_surjective (f := q) hq).trans
      ((Subgroup.card_dvd_of_le hH).trans (Subgroup.card_range_dvd p))
    have hc : Nat.card (⊤ : Subgroup (AffineGroup F d)) = Nat.card (AffineGroup F d) :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← hc] at hdvd
    exact (affine_alternating_section_bound ⊤ hk hdvd).trans (le_max_right _ _)
  · exact (show (k : ℝ) ≤ 63 by exact_mod_cast (show k ≤ 63 by omega)).trans
      (le_max_left _ _)

/-- Here the logarithm is explicitly the physical vector-space degree. -/
theorem natural_affine_alternating_quotient_bound
    (H : Subgroup (Equiv.Perm (Fin d → F)))
    (hH : H ≤ BudgetInduction.affineImage F d)
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q) :
    (k : ℝ) ≤ max 63
      ((12 / Real.log 2) * Real.log (Fintype.card (Fin d → F))) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    affine_image_alternating_quotient_bound
      (BudgetInduction.affineActionHom F d) H hH q hq

end GI.A15Work
