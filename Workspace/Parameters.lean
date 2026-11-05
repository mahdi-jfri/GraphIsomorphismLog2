module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GI

/-- The example scale parameters in Section 7.5 meet the stated strict inequalities. -/
theorem paper_scale_parameters :
    (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) < 1 / 2 ∧
    2 * (2 / 5 : ℝ) < 9 / 10 ∧ (9 / 10 : ℝ) < 1 ∧
    1 - (2 / 5 : ℝ) < 9 / 10 ∧ 1 - 2 * (2 / 5 : ℝ) < 2 / 5 := by
  norm_num

theorem paper_cap_parameters :
    (0 : ℝ) < 1 / 4 ∧ (2 / 3 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 ∧
    (1 / 2 : ℝ) < 9 / 10 ∧ 1 - (1 / 4 : ℝ) < 9 / 10 ∧
    1 - (3 / 4 : ℝ) * (1 / 4) < 9 / 10 ∧ (3 / 4 : ℝ) < 9 / 10 ∧
    (9 / 10 : ℝ) < 1 ∧ (1 / 2 : ℝ) < 3 / 4 ∧
    2 * (3 / 4 : ℝ) * (1 - 3 / 4) < 3 / 4 := by
  norm_num

/-- The unordered-pair rectangle ratio is at most theta for these parameters and q >= 2. -/
theorem rectangle_ratio_bound {q : ℝ} (hq : 2 ≤ q) :
    2 * (3 / 4 : ℝ) * (1 - 3 / 4) * q / (q - 1) ≤ 3 / 4 := by
  apply (div_le_iff₀ (by linarith : 0 < q - 1)).2
  linarith

/-- Removing all but a fixed fraction of labels bounds the rectangle area. -/
theorem rectangle_area_bound {w r c eta : ℝ} (hc : 0 ≤ c)
    (heta : (1 / 2 : ℝ) ≤ eta) (hw : eta * c ≤ w)
    (hr : r ≤ c - w) :
    w * r ≤ eta * (1 - eta) * c ^ 2 := by
  have hw0 : 0 ≤ w := le_trans (mul_nonneg (by linarith) hc) hw
  have h1 := mul_le_mul_of_nonneg_left hr hw0
  have h2 : 0 ≤ (w - eta * c) * (w + eta * c - c) := by
    apply mul_nonneg (by linarith)
    have hhalf := mul_le_mul_of_nonneg_right heta hc
    linarith
  nlinarith

end GI
