module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The Cameron range not covered by [H, Section 2.8]

Section A.5, "Constructive recognition": "For the Johnson recognition procedure in that
source, the range not covered by its simple polynomial construction has entire constituent
order `d^{O(log d)}`, where `d` is the physical interval degree." The source is
[H] = Helfgott, Bajpai, Dona, arXiv:1710.04574v1, Section 2.8: "We will suppose that
`m > (k+1)² − 2`", with footnote (14): "If `m ≤ (k+1)² − 2`, then `n` is so large that
`m! = n^{O(log n)}`." [H] gives no proof, so the claim is the paper's own and is proved here.

The constituent is a subgroup of `Sym(m) wr Sym(r)` in its product action on `r`-tuples of
`k`-subsets, of degree `d = binom(m,k)^r`. Its order is at most `(m!)^r r!`. The Johnson
scheme `J(m, k)` is the same as `J(m, m - k)`, so [H] assumes `2k ≤ m`; the claim needs this
(for `k = m - 1` the condition `m ≤ (k+1)² - 2` always holds, while `m! ` is not
`m^{O(log m)}`).

**Claim** (`cameron_range_order`). If `1 ≤ k`, `2k ≤ m`, `m ≤ (k+1)² - 2` and `r ≥ 1`, then
`(m!)^r r! ≤ exp(103 (log d)²) = d^{103 log d}` with `d = binom(m,k)^r`.

*Proof.* Put `b = binom(m,k)` and `j = ⌊√m⌋`. From `m < (k+1)²` we get `j ≤ k`. Two lower
bounds for `log b`:
* `b ≥ binom(2k, k) ≥ 2^k`, so `log b ≥ k log 2 ≥ j log 2`;
* `b ≥ binom(m, j) ≥ (m+1-j)^j / j^j ≥ (m/2)^j / m^{j/2}` (monotonicity of `binom(m, ·)`
  below `m/2`, and `j² ≤ m`), so `log b ≥ j (½ log m - log 2)`, which is at least
  `(j/4) log m` when `m ≥ 16`.
Multiplying, and using `4 j² > m`, gives `(log b)² ≥ (log 2 / 16) m log m` for `m ≥ 16`; for
`m < 16` directly `m log m ≤ 64 log 2 ≤ 93 (log 2)² ≤ 93 (log b)²`. Hence
`log m! ≤ m log m ≤ 100 (log b)²`. Finally `log r! ≤ r log r ≤ r² ≤ 3 r² (log b)²`, so
`log((m!)^r r!) ≤ 100 r (log b)² + 3 r² (log b)² ≤ 103 (r log b)² = 103 (log d)²`.
-/

namespace GI.CameronRange

open Real

/-- `binom(m, ·)` is monotone below `m/2`. -/
theorem choose_le_choose_of_le_half {m j k : ℕ} (hjk : j ≤ k) (hk : 2 * k ≤ m) :
    m.choose j ≤ m.choose k := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · have h1 := ih (Nat.lt_succ_iff.1 h) (by omega)
      exact h1.trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem two_mul_le_two_pow : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ 2 ^ k
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num
  | k + 2, _ => by
    have := two_mul_le_two_pow (k + 1) (by omega)
    have h2 : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
    rw [pow_succ]; omega

/-- `2^k ≤ binom(m, k)` for `2k ≤ m`. -/
theorem two_pow_le_choose {m k : ℕ} (hk : 2 * k ≤ m) : 2 ^ k ≤ m.choose k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom k hk0
  rw [Nat.centralBinom_eq_two_mul_choose] at h4
  have hmono : (2 * k).choose k ≤ m.choose k := Nat.choose_le_choose k hk
  -- `4^k ≤ 2k · binom(2k,k)` and `2k ≤ 2^k`.
  have h2k : 2 * k ≤ 2 ^ k := two_mul_le_two_pow k hk0
  have h4' : 2 ^ k * 2 ^ k ≤ 2 ^ k * (2 * k).choose k := by
    calc 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
      _ ≤ 2 * k * (2 * k).choose k := h4
      _ ≤ 2 ^ k * (2 * k).choose k := Nat.mul_le_mul_right _ h2k
  exact (Nat.le_of_mul_le_mul_left h4' (by positivity)).trans hmono

/-- `binom(m, j) · j^j ≥ (m + 1 - j)^j`. -/
theorem pow_le_choose_mul_pow (m j : ℕ) : (m + 1 - j) ^ j ≤ m.choose j * j ^ j := by
  have h1 := Nat.pow_sub_le_descFactorial m j
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  calc (m + 1 - j) ^ j ≤ j.factorial * m.choose j := h1
    _ ≤ j ^ j * m.choose j := Nat.mul_le_mul_right _ (Nat.factorial_le_pow j)
    _ = m.choose j * j ^ j := Nat.mul_comm _ _

theorem log_two_gt : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9

/-- `log m! ≤ 100 (log binom(m,k))²` in the range `1 ≤ k`, `2k ≤ m`, `m + 2 ≤ (k+1)²`. -/
theorem log_factorial_le {m k : ℕ} (hk : 1 ≤ k) (hkm : 2 * k ≤ m) (hm : m + 2 ≤ (k + 1) ^ 2) :
    log (m.factorial : ℝ) ≤ 100 * log (m.choose k : ℝ) ^ 2 := by
  have hl2 := log_two_gt
  set b := m.choose k with hb
  have hb2 : 2 ≤ b := le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hk)
    (two_pow_le_choose hkm)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hm2 : 2 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- `log m! ≤ m log m`
  have hfact : log (m.factorial : ℝ) ≤ m * log m := by
    have h := Nat.factorial_le_pow m
    have h' : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast h
    calc log (m.factorial : ℝ) ≤ log ((m : ℝ) ^ m) :=
          log_le_log (by exact_mod_cast Nat.factorial_pos m) h'
      _ = m * log m := by rw [log_pow]
  -- `k log 2 ≤ log b`
  have hL1 : (k : ℝ) * log 2 ≤ log b := by
    have h : ((2 : ℝ) ^ k) ≤ b := by exact_mod_cast two_pow_le_choose hkm
    calc (k : ℝ) * log 2 = log ((2 : ℝ) ^ k) := by rw [log_pow]
      _ ≤ log b := log_le_log (by positivity) h
  have hL0 : log 2 ≤ log b := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  refine hfact.trans ?_
  by_cases h16 : m < 16
  · -- small `m`: `m log m ≤ 16 log 16 = 64 log 2 ≤ 100 (log 2)²`
    have hm16 : (m : ℝ) ≤ 16 := by exact_mod_cast h16.le
    have hlogm : log m ≤ 4 * log 2 := by
      calc log (m : ℝ) ≤ log 16 := log_le_log hmpos hm16
        _ = 4 * log 2 := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
    have hlogm0 : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    calc (m : ℝ) * log m ≤ 16 * (4 * log 2) := mul_le_mul hm16 hlogm hlogm0 (by norm_num)
      _ ≤ 100 * log 2 ^ 2 := by nlinarith
      _ ≤ 100 * log b ^ 2 := by
          have : 0 ≤ log 2 := by linarith
          nlinarith
  · push Not at h16
    set j := Nat.sqrt m with hj
    have hjk : j ≤ k := by
      have : m < (k + 1) ^ 2 := by omega
      exact Nat.lt_succ_iff.1 (Nat.sqrt_lt'.2 this)
    have hj1 : 1 ≤ j := Nat.le_sqrt'.2 (by omega)
    have hjsq : j ^ 2 ≤ m := Nat.sqrt_le' m
    have hm4 : m < 4 * j ^ 2 := by
      have := Nat.lt_succ_sqrt' m
      rw [← hj] at this
      nlinarith
    -- `log binom(m, j) ≥ j (log(m/2) - log j)`
    have hjm : 2 * j ≤ m := by omega
    have hcj := pow_le_choose_mul_pow m j
    have hcjb : m.choose j ≤ b := choose_le_choose_of_le_half hjk hkm
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hsub : ((m + 1 - j : ℕ) : ℝ) ≥ (m : ℝ) / 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast
      have : (2 : ℝ) * j ≤ m := by exact_mod_cast hjm
      linarith
    have hlogj : 2 * log (j : ℝ) ≤ log m := by
      have : ((j : ℝ) ^ 2) ≤ m := by exact_mod_cast hjsq
      calc 2 * log (j : ℝ) = log ((j : ℝ) ^ 2) := by rw [log_pow]; norm_num
        _ ≤ log m := log_le_log (by positivity) this
    have hL2 : (j : ℝ) * (log m - log 2 - log j) ≤ log b := by
      have h1 : ((m : ℝ) / 2) ^ j ≤ (b : ℝ) * (j : ℝ) ^ j := by
        have e1 : ((m : ℝ) / 2) ^ j ≤ ((m + 1 - j : ℕ) : ℝ) ^ j :=
          pow_le_pow_left₀ (by positivity) hsub j
        have e2 : (((m + 1 - j) ^ j : ℕ) : ℝ) ≤ ((m.choose j * j ^ j : ℕ) : ℝ) := by
          exact_mod_cast hcj
        have e3 : ((m.choose j : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hcjb
        push_cast at e2
        calc ((m : ℝ) / 2) ^ j ≤ ((m + 1 - j : ℕ) : ℝ) ^ j := e1
          _ ≤ (m.choose j : ℝ) * (j : ℝ) ^ j := e2
          _ ≤ (b : ℝ) * (j : ℝ) ^ j := mul_le_mul_of_nonneg_right e3 (by positivity)
      have h2 := log_le_log (by positivity) h1
      rw [log_pow, log_mul hbpos.ne' (by positivity), log_pow, log_div hmpos.ne' (by norm_num)]
        at h2
      linarith
    have hlog16 : 4 * log 2 ≤ log m := by
      have : (16 : ℝ) ≤ m := by exact_mod_cast h16
      calc 4 * log 2 = log 16 := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
        _ ≤ log m := log_le_log (by norm_num) this
    -- `log b ≥ (j/4) log m` and `log b ≥ j log 2`
    have hA : (j : ℝ) / 4 * log m ≤ log b := by
      have : (j : ℝ) / 4 * log m ≤ (j : ℝ) * (log m - log 2 - log j) := by
        have : log m / 4 ≤ log m - log 2 - log j := by linarith
        nlinarith
      linarith
    have hB : (j : ℝ) * log 2 ≤ log b := by
      have : (j : ℝ) ≤ k := by exact_mod_cast hjk
      nlinarith
    have hlogm0 : 0 ≤ log (m : ℝ) := by linarith
    have hprod : ((j : ℝ) / 4 * log m) * ((j : ℝ) * log 2) ≤ log b * log b :=
      mul_le_mul hA hB (by positivity) (by linarith)
    have hm4' : (m : ℝ) ≤ 4 * (j : ℝ) ^ 2 := by exact_mod_cast hm4.le
    -- `m log m ≤ (16 / log 2) (log b)² ≤ 100 (log b)²`
    have : (m : ℝ) * log m * log 2 ≤ 16 * log b ^ 2 := by
      have h1 : (m : ℝ) * log m * log 2 ≤ 4 * (j : ℝ) ^ 2 * log m * log 2 := by
        have := mul_le_mul_of_nonneg_right hm4' hlogm0
        nlinarith
      nlinarith
    nlinarith

/-- **The Cameron range has order `d^{O(log d)}`** (Section A.5, "Constructive recognition";
[H, Section 2.8], footnote 14). If `1 ≤ k`, `2k ≤ m`, `m ≤ (k+1)² - 2` and `r ≥ 1`, then
`|Sym(m) wr Sym(r)| = (m!)^r r! ≤ exp(103 (log d)²)`, `d = binom(m,k)^r`. -/
theorem cameron_range_order {m k r : ℕ} (hk : 1 ≤ k) (hkm : 2 * k ≤ m)
    (hm : m + 2 ≤ (k + 1) ^ 2) (hr : 1 ≤ r) :
    ((m.factorial ^ r * r.factorial : ℕ) : ℝ) ≤
      exp (103 * log ((m.choose k ^ r : ℕ) : ℝ) ^ 2) := by
  have hl2 := log_two_gt
  set b := m.choose k
  have hb2 : 2 ≤ b := le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hk)
    (two_pow_le_choose hkm)
  have hL0 : log 2 ≤ log (b : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hb2)
  have hmf : log (m.factorial : ℝ) ≤ 100 * log (b : ℝ) ^ 2 := log_factorial_le hk hkm hm
  have hpos : (0 : ℝ) < ((m.factorial ^ r * r.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (Nat.factorial_pos m) r) (Nat.factorial_pos r)
  rw [← exp_log hpos, exp_le_exp]
  push_cast
  rw [log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos r).ne'), log_pow, log_pow]
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  -- `log r! ≤ r log r ≤ r²`
  have hrf : log (r.factorial : ℝ) ≤ (r : ℝ) ^ 2 := by
    have h := Nat.factorial_le_pow r
    have h' : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast h
    have hlr : log (r : ℝ) ≤ r := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    calc log (r.factorial : ℝ) ≤ log ((r : ℝ) ^ r) :=
          log_le_log (by exact_mod_cast Nat.factorial_pos r) h'
      _ = r * log r := by rw [log_pow]
      _ ≤ r * r := mul_le_mul_of_nonneg_left hlr (by linarith)
      _ = (r : ℝ) ^ 2 := by ring
  have hsq : (1 : ℝ) / 3 ≤ log (b : ℝ) ^ 2 := by nlinarith
  have hLb : 0 ≤ log (b : ℝ) ^ 2 := sq_nonneg _
  have h1 : (r : ℝ) * log (m.factorial : ℝ) ≤ 100 * (r : ℝ) ^ 2 * log (b : ℝ) ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hmf (by linarith : (0 : ℝ) ≤ r)
    have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h4 : (r : ℝ) * (100 * log (b : ℝ) ^ 2) ≤ (r : ℝ) ^ 2 * (100 * log (b : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hrr (by positivity)
    linarith
  have h2 : (r : ℝ) ^ 2 ≤ 3 * (r : ℝ) ^ 2 * log (b : ℝ) ^ 2 := by nlinarith
  nlinarith

end GI.CameronRange
