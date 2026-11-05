module

public import Workspace.Cited.GMP
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Degree inequalities for the GMP bound

The imprimitive induction multiplies two bounds of the form `n ^ logb 2 n`.
In the nonabelian primitive cases, a power-of-two degree bound pays for
the factorial of the number of socle factors and, when needed, one copy
of the degree itself.
-/

namespace GI.Proved

/-- The target degree bound is at least one, including degree one. -/
theorem gmp_one_le_degree_bound {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.one_le_rpow hnR (Real.logb_nonneg (by norm_num) hnR)

/-- Multiplying the induction bounds for a block size and a block count
stays within the bound for their product. -/
theorem gmp_degree_bound_mul {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    s ^ Real.logb 2 s * t ^ Real.logb 2 t ≤
      (s * t) ^ Real.logb 2 (s * t) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hsle : s ≤ s * t := by simpa using mul_le_mul_of_nonneg_left ht hs0.le
  have htle : t ≤ s * t := by simpa using mul_le_mul_of_nonneg_right hs ht0.le
  rw [Real.mul_rpow hs0.le ht0.le]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hs
      (Real.logb_le_logb_of_le (by norm_num) hs0 hsle))
    (Real.rpow_le_rpow_of_exponent_le ht
      (Real.logb_le_logb_of_le (by norm_num) ht0 htle))
    (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hs0.le _)

/-- An integral power-of-two degree bound gives the needed logarithmic bound. -/
theorem gmp_exponent_le_logb {n r : ℕ} (h : 2 ^ r ≤ n) :
    (r : ℝ) ≤ Real.logb 2 n := by
  have hR : (2 : ℝ) ^ r ≤ (n : ℝ) := by exact_mod_cast h
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) r) hR
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] using hlog

/-- The same degree bound pays for `r!` and `d` copies of the degree. -/
theorem gmp_factorial_degree_bound {n r d : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ (r + d) ≤ n) :
    (n : ℝ) ^ d * (r.factorial : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  have hrd : r ≤ r + d := Nat.le_add_right r d
  have hrn : r ≤ n :=
    (Nat.le_of_lt r.lt_two_pow_self).trans
      ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrd).trans h)
  have hfac : r.factorial ≤ n ^ r :=
    (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left hrn r)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (n : ℝ) ^ d * (r.factorial : ℝ) ≤ (n : ℝ) ^ d * (n : ℝ) ^ r :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hfac) (pow_nonneg (by positivity) _)
    _ = (n : ℝ) ^ (r + d) := by rw [← pow_add, Nat.add_comm]
    _ ≤ (n : ℝ) ^ Real.logb 2 n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hnR (gmp_exponent_le_logb h)

end GI.Proved
