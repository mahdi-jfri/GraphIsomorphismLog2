import Workspace.BudgetInductionAffine
import Workspace.BudgetInductionAlternatives

namespace GI.BudgetInduction

open MatrixValuation

/-- Actual affine-group images furnish the order-valuation alternative.
There is no recognition assumption or desired sigma bound in this proof. -/
theorem primitive_alternative_of_affine_image {F : Type*} [Field F] [Fintype F]
    {d n : ℕ} {A₀ : ℝ} (hA : 12 / Real.log 2 ≤ A₀)
    (p : AffineGroup F d →* Equiv.Perm (Fin n))
    (hdegree : n = (Fintype.card F) ^ d)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ≤ p.range) :
    PrimitiveReductionAlternative A₀ H := by
  obtain ⟨q, hq, hv⟩ := affine_subgroup_uniform_bound F d ⊤
  have hc : Nat.card (⊤ : Subgroup (AffineGroup F d)) = Nat.card (AffineGroup F d) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hc] at hv
  haveI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
  have hdvd := (Subgroup.card_dvd_of_le hH).trans (Subgroup.card_range_dvd p)
  have hm := primeValuation_mono (p := q)
    (Nat.ne_of_gt (Nat.card_pos (α := AffineGroup F d))) hdvd
  have hmr : (padicValNat q (Nat.card H) : ℝ) ≤
      padicValNat q (Nat.card (AffineGroup F d)) := by exact_mod_cast hm
  have hv' : 6 * (padicValNat q (Nat.card (AffineGroup F d)) : ℝ) ≤
      (12 / Real.log 2) * Real.log n := by
    simpa only [hdegree, Nat.cast_pow] using hv
  exact Or.inl ⟨q, hq,
    ((mul_le_mul_of_nonneg_left hmr (by norm_num)).trans hv').trans
      (mul_le_mul_of_nonneg_right hA (Real.log_natCast_nonneg n))⟩

end GI.BudgetInduction
