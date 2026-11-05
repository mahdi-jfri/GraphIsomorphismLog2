module

public import Workspace.BinomialLower
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace GI.Johnson

theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem log_two_lower : (693 / 1000 : ℝ) < Real.log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

theorem log_three_lower : (1579 / 1500 : ℝ) < Real.log 3 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  rw [Real.log_div (by norm_num) (by norm_num), log_four_eq] at h
  have htwo := log_two_lower
  linarith

theorem budget_constants {C : ℝ} (hC : 128 ≤ C) :
    3 ≤ C * (Real.log 4 - 1) ∧ 6 < C * (Real.log 3 - 1) ∧ 3 ≤ C + 6 := by
  have htwo := log_two_lower
  have hthree := log_three_lower
  have hfour : 0 ≤ Real.log 4 - 1 := by rw [log_four_eq]; linarith
  have hthree' : 0 ≤ Real.log 3 - 1 := by linarith
  have h₁ := mul_le_mul_of_nonneg_right hC hfour
  have h₂ := mul_le_mul_of_nonneg_right hC hthree'
  rw [log_four_eq] at h₁
  constructor
  · rw [log_four_eq]
    nlinarith
  constructor
  · nlinarith
  · linarith

theorem fresh_budget_pos {C w : ℝ} (hC : 128 ≤ C) (hw : 3 ≤ w) :
    0 < C * Real.log w - (C + 6) := by
  have h := (budget_constants hC).2.1
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hw
  have hm := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ C)
  nlinarith

/-- The derivative estimate used in A.7, obtained directly from log's
tangent inequality, so no differentiability side conditions are hidden. -/
theorem entropy_increment_lower {m r t : ℝ}
    (hr : 0 < r) (hrt : r ≤ t) (htm : 4 * t ≤ m) :
    (t - r) * (Real.log 4 - 1) ≤
      t * Real.log (m / t) - r * Real.log (m / r) := by
  have ht : 0 < t := hr.trans_le hrt
  have hm : 0 < m := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hr)
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have hcancel : r * (t / r - 1) = t - r := by field_simp
  rw [hcancel] at hmul
  have hratio : (4 : ℝ) ≤ m / t := (le_div_iff₀ ht).mpr htm
  have hlogratio := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
  have hbound := mul_le_mul_of_nonneg_left hlogratio (sub_nonneg.mpr hrt)
  have he : t * Real.log (m / t) - r * Real.log (m / r) =
      (t - r) * Real.log (m / t) - r * Real.log (t / r) := by
    rw [Real.log_div hm.ne' ht.ne', Real.log_div hm.ne' hr.ne',
      Real.log_div ht.ne' hr.ne']
    ring
  rw [he]
  nlinarith

/-- Combining the actual forest charge expression with the binomial
logarithm bound in the small-subset regime. -/
theorem small_subset_charge_bound {C m r t L : ℝ}
    (hC : 128 ≤ C) (hr : 1 ≤ r) (hrt : r ≤ t) (htm : 4 * t ≤ m)
    (hL : t * Real.log (m / t) ≤ L) :
    C * (r * Real.log (m / r) + r - 1) - (C + 6) * r + 3 * (t - 1) ≤
      C * L - (C + 6) := by
  have hc0 : 0 ≤ C := by linarith
  have he := entropy_increment_lower (by linarith : 0 < r) hrt htm
  have hm := mul_le_mul_of_nonneg_left he hc0
  have hk := mul_le_mul_of_nonneg_left (budget_constants hC).1 (sub_nonneg.mpr hrt)
  have hl := mul_le_mul_of_nonneg_left hL hc0
  nlinarith

/-- The large-subset regime absorbs the direct order-valuation charge. -/
theorem large_subset_charge_bound {C m t L : ℝ}
    (hC : 128 ≤ C) (hm : 64 ≤ m) (htlow : m ≤ 4 * t) (hthigh : 2 * t ≤ m)
    (hL : t * Real.log (m / t) ≤ L) :
    3 * m ≤ C * L - (C + 6) := by
  have ht : 0 < t := by linarith
  have hratio : (2 : ℝ) ≤ m / t := (le_div_iff₀ ht).mpr hthigh
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by have h := log_two_lower; linarith
  have hprod := mul_le_mul_of_nonneg_left (htwo.trans hlog) ht.le
  have hL' : m / 6 ≤ L := by nlinarith
  have hc0 : 0 ≤ C := by linarith
  have ha := mul_le_mul_of_nonneg_left hL' hc0
  have hb := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ m / 6 - 1)
  nlinarith

/-- The anchor-position charge alone fits the target bound, including when
there are no charged natural orbits or the original degree is below cutoff. -/
theorem anchor_only_charge_bound {C m t L : ℝ}
    (hC : 128 ≤ C) (ht : 2 ≤ t) (hthigh : 2 * t ≤ m)
    (hL : t * Real.log (m / t) ≤ L) :
    3 * (t - 1) ≤ C * L - (C + 6) := by
  have htp : 0 < t := by linarith
  have hratio : (2 : ℝ) ≤ m / t := (le_div_iff₀ htp).mpr hthigh
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by have h := log_two_lower; linarith
  have hprod := mul_le_mul_of_nonneg_left (htwo.trans hlog) htp.le
  have hL' : (2 / 3 : ℝ) * t ≤ L := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hL' (by linarith : 0 ≤ C)
  have hb := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ (2 / 3 : ℝ) * t - 1)
  nlinarith

end GI.Johnson
