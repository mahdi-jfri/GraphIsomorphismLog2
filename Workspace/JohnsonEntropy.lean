import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace GI.Johnson

/-- The two-term log-sum inequality, proved from the tangent inequality for log. -/
theorem log_sum_two {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) :
    a * Real.log (x / a) + b * Real.log (y / b) ≤
      (a + b) * Real.log ((x + y) / (a + b)) := by
  have hr := add_pos ha hb
  have hw := add_pos hx hy
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (mul_pos hx hr) (mul_pos ha hw))) ha.le
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (mul_pos hy hr) (mul_pos hb hw))) hb.le
  have hzero : a * (x * (a + b) / (a * (x + y)) - 1) +
      b * (y * (a + b) / (b * (x + y)) - 1) = 0 := by
    field_simp
    ring
  have hs := add_le_add h₁ h₂
  rw [hzero] at hs
  rw [Real.log_div (mul_pos hx hr).ne' (mul_pos ha hw).ne',
    Real.log_div (mul_pos hy hr).ne' (mul_pos hb hw).ne',
    Real.log_mul hx.ne' hr.ne', Real.log_mul ha.ne' hw.ne',
    Real.log_mul hy.ne' hr.ne', Real.log_mul hb.ne' hw.ne'] at hs
  rw [Real.log_div hx.ne' ha.ne', Real.log_div hy.ne' hb.ne',
    Real.log_div hw.ne' hr.ne']
  nlinarith

noncomputable def forestPotential (w r : ℝ) : ℝ := r * Real.log (w / r) + (r - 1)

/-- Losing untracked mass along a continuing path preserves the entropy bound. -/
theorem unary_entropy_step {w x r : ℝ} (hx : 0 < x) (hxr : x ≤ w) (hr : 1 ≤ r) :
    Real.log (w / x) + forestPotential x r ≤ forestPotential w r := by
  have hw : 0 < w := hx.trans_le hxr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hd : 0 ≤ Real.log (w / x) :=
    Real.log_nonneg ((one_le_div hx).mpr hxr)
  have he : Real.log (w / r) = Real.log (w / x) + Real.log (x / r) := by
    rw [Real.log_div hw.ne' hrp.ne', Real.log_div hw.ne' hx.ne',
      Real.log_div hx.ne' hrp.ne']
    ring
  have hm := mul_le_mul_of_nonneg_right hr hd
  simp only [one_mul] at hm
  unfold forestPotential
  rw [he]
  nlinarith

/-- Binary refinement entropy step when the larger child continues the old token.
Iterating binary splits also represents an arbitrary finite multiway split. -/
theorem binary_entropy_step {w x y a b : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hmass : x + y ≤ w) (hlargest : y ≤ x) (hr : 1 ≤ a + b) :
    Real.log (w / x) + forestPotential x a + forestPotential y b ≤
      forestPotential w (a + b) := by
  have hs := add_pos hx hy
  have hw : 0 < w := hs.trans_le hmass
  have hab := add_pos ha hb
  have hsum := log_sum_two ha hb hx hy
  have hd : 0 ≤ Real.log (w / (x + y)) :=
    Real.log_nonneg ((one_le_div hs).mpr hmass)
  have htwo : Real.log ((x + y) / x) ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hs hx)
    have hd₂ : (x + y) / x ≤ 2 := (div_le_iff₀ hx).mpr (by linarith)
    linarith
  have hlog : Real.log (w / x) =
      Real.log (w / (x + y)) + Real.log ((x + y) / x) := by
    rw [Real.log_div hw.ne' hx.ne', Real.log_div hw.ne' hs.ne',
      Real.log_div hs.ne' hx.ne']
    ring
  have hparent : Real.log (w / (a + b)) =
      Real.log ((x + y) / (a + b)) + Real.log (w / (x + y)) := by
    rw [Real.log_div hw.ne' hab.ne', Real.log_div hs.ne' hab.ne',
      Real.log_div hw.ne' hs.ne']
    ring
  have hm := mul_le_mul_of_nonneg_right hr hd
  simp only [one_mul] at hm
  unfold forestPotential
  rw [hlog, hparent]
  nlinarith

end GI.Johnson
