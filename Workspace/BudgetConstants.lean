module

public import Workspace.JohnsonNumerics

@[expose] public section

namespace GI

/-- The coefficient choice after the primitive valuation constant in A.9.
This proves the arithmetic choice, not the primitive valuation theorem. -/
theorem exists_budget_coefficient (A₀ : ℝ) (hA : 0 ≤ A₀) :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      A₀ * Real.log x ≤ C * Real.log x - (C + 6) := by
  have hd : 0 < Real.log 3 - 1 := by
    have h := Johnson.log_three_lower
    linarith
  let t := (A₀ + 6) / (Real.log 3 - 1)
  have ht : 0 ≤ t := div_nonneg (by linarith) hd.le
  have htd : t * (Real.log 3 - 1) = A₀ + 6 := div_mul_cancel₀ _ hd.ne'
  let C := A₀ + t + 128
  have hC : 128 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hnonneg : 0 ≤ C - A₀ := by dsimp [C]; linarith
  have hbase : A₀ + 6 ≤ (C - A₀) * (Real.log 3 - 1) := by
    dsimp [C]
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx
  have hmul := mul_le_mul_of_nonneg_left hlog hnonneg
  nlinarith

end GI
