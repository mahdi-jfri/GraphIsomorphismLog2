module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The counting inequalities behind the bounds of Section A (`sec:quotient-algorithms`)

* `count_le_exp`: a recursion of depth `ℓ ≤ 5 log₃ b + 1` with at most `4M³ + 2` children
  per call has at most `exp(42 log(b+M+2) log(b+2))` calls (Theorem A.20).
* `poly_le_exp`: a polynomial factor `(b+M+2)^k` is `exp(2k log(b+M+2) log(b+2))`.
* `index_le_exp`: `b^{2 log₂ b} ≤ exp(3 log²(b+2))` (the radical index in Corollary A.22).
* `log_add_le`: `log(b+M+2) ≤ log(b+2) + log(M+2)`.
-/

namespace GI.Multicoset

open Real

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem log_two_le_log_add_two (b : ℕ) : Real.log 2 ≤ Real.log ((b : ℝ) + 2) :=
  Real.log_le_log (by norm_num) (by have : (0 : ℝ) ≤ b := Nat.cast_nonneg b; linarith)

theorem logb_three_le (b : ℕ) : Real.logb 3 b ≤ Real.log ((b : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp only [Nat.cast_zero, Real.logb_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  · have hb : (1 : ℝ) ≤ b := by exact_mod_cast h
    have hlog : 0 ≤ Real.log b := Real.log_nonneg hb
    rw [Real.logb]
    calc Real.log b / Real.log 3 ≤ Real.log b :=
          div_le_self hlog one_le_log_three
      _ ≤ Real.log ((b : ℝ) + 2) := Real.log_le_log (by linarith) (by linarith)

/-- The depth bound: `5 log₃ b + 1 ≤ 7 log(b+2)`. -/
theorem depth_le (b : ℕ) : 5 * Real.logb 3 b + 1 ≤ 7 * Real.log ((b : ℝ) + 2) := by
  have h1 := logb_three_le b
  have h2 := log_two_le_log_add_two b
  have h3 := half_le_log_two
  linarith

theorem log_branch_le (b M : ℕ) :
    Real.log (4 * (M : ℝ) ^ 3 + 2) ≤ 6 * Real.log ((b : ℝ) + M + 2) := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rw [show (6 : ℝ) * Real.log ((b : ℝ) + M + 2) = ((6 : ℕ) : ℝ) * Real.log ((b : ℝ) + M + 2)
    by norm_num, ← Real.log_pow]
  apply Real.log_le_log (by positivity)
  have h1 : 4 * (M : ℝ) ^ 3 + 2 ≤ ((M : ℝ) + 2) ^ 6 := by
    nlinarith [pow_nonneg hM 3, pow_nonneg hM 4, pow_nonneg hM 5, pow_nonneg hM 6,
      pow_nonneg hM 2]
  exact h1.trans (pow_le_pow_left₀ (by positivity) (by linarith) 6)

/-- **The counting inequality of Theorem A.20.** -/
theorem count_le_exp (b M ℓ : ℕ) (hℓ : (ℓ : ℝ) ≤ 5 * Real.logb 3 b + 1) :
    ((4 * M ^ 3 + 2) ^ ℓ : ℕ) ≤
      Real.exp (42 * Real.log ((b : ℝ) + M + 2) * Real.log ((b : ℝ) + 2)) := by
  have hpos : (0 : ℝ) < 4 * (M : ℝ) ^ 3 + 2 := by positivity
  push_cast
  rw [← Real.exp_log (pow_pos hpos ℓ), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hd := hℓ.trans (depth_le b)
  have hbr := log_branch_le b M
  have hl0 : 0 ≤ Real.log (4 * (M : ℝ) ^ 3 + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
    linarith)
  have hL : 0 ≤ Real.log ((b : ℝ) + 2) :=
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans (log_two_le_log_add_two b)
  calc (ℓ : ℝ) * Real.log (4 * (M : ℝ) ^ 3 + 2)
      ≤ (7 * Real.log ((b : ℝ) + 2)) * (6 * Real.log ((b : ℝ) + M + 2)) :=
        mul_le_mul hd hbr hl0 (by positivity)
    _ = 42 * Real.log ((b : ℝ) + M + 2) * Real.log ((b : ℝ) + 2) := by ring

/-- A polynomial factor `(b+M+2)^k` costs `exp(2k log(b+M+2) log(b+2))`. -/
theorem poly_le_exp (b M k : ℕ) :
    (((b + M + 2) ^ k : ℕ) : ℝ) ≤
      Real.exp (2 * k * Real.log ((b : ℝ) + M + 2) * Real.log ((b : ℝ) + 2)) := by
  have hpos : (0 : ℝ) < (b : ℝ) + M + 2 := by positivity
  push_cast
  rw [← Real.exp_log (pow_pos hpos k), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have h2 := log_two_le_log_add_two b
  have h3 := half_le_log_two
  have hl : 0 ≤ Real.log ((b : ℝ) + M + 2) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) M])
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hk hl]

theorem log_add_le (b M : ℕ) :
    Real.log ((b : ℝ) + M + 2) ≤ Real.log ((b : ℝ) + 2) + Real.log ((M : ℝ) + 2) := by
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rw [← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- `b^{2 log₂ b} ≤ exp(3 log²(b+2))`. -/
theorem index_le_exp (b : ℕ) :
    (b : ℝ) ^ (2 * Real.logb 2 b) ≤ Real.exp (3 * Real.log ((b : ℝ) + 2) ^ 2) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h
    simp only [Nat.cast_zero, Real.logb_zero, mul_zero, Real.rpow_zero]
    exact Real.one_le_exp (by positivity)
  · have hb : (0 : ℝ) < b := by exact_mod_cast h
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast h
    rw [Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hle : Real.log b ≤ Real.log ((b : ℝ) + 2) := Real.log_le_log hb (by linarith)
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [Real.logb]
    have hdiv : Real.log b / Real.log 2 ≤ 3 / 2 * Real.log b := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    calc Real.log b * (2 * (Real.log b / Real.log 2))
        ≤ Real.log b * (2 * (3 / 2 * Real.log b)) :=
          mul_le_mul_of_nonneg_left (by linarith) hlb
      _ = 3 * Real.log b ^ 2 := by ring
      _ ≤ 3 * Real.log ((b : ℝ) + 2) ^ 2 := by
          have := pow_le_pow_left₀ hlb hle 2
          linarith

end GI.Multicoset
