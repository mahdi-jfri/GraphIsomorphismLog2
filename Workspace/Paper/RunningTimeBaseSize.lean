module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Workspace.BinomialLower

@[expose] public section

/-!
# Section 7.5: the absolute base size `N₀`

The last paragraph of Section 7.5 of the paper asks for an
absolute base size `N₀` such that, for every `N ≥ N₀`,
`C(⌊N^α⌋,3) > N`, `C(⌊N^α⌋,2) > N^{1-α}`, `N^α > q₀`, the row threshold admits an
odd integer `k > max{8, 2 + log₂ N}` with `2k - 1 ≤ N^α`, `N^γ ≥ 6`, `⌈N^γ⌉ < N`, and
`N^{γD-a} ≥ 2`. It says: "These inequalities hold eventually because `3α > 1` and a
positive power of `N` dominates `log N`." This file proves that.
-/

namespace GI.Paper

open Filter Real

theorem eventually_rpow_ge {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c ≤ (N : ℝ) ^ ε :=
  ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `log N ≤ c N^α` eventually, for `c > 0` and `α > 0`. -/
theorem eventually_log_le_rpow {α : ℝ} (hα : 0 < α) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log N ≤ c * (N : ℝ) ^ α := by
  have h := (isLittleO_log_rpow_atTop hα).bound hc
  have h2 := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [Real.norm_of_nonneg (Real.log_nonneg hN1'),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hN
  exact hN

/-- The base size of Section 7.5. For `1/3 < α < 1/2`, `2α < γ < 1`, any `q₀`, and
`a < γD` (which holds when `D > a/γ + 2`), there is `N₀` such that for every
`N ≥ N₀` all the listed conditions hold. -/
theorem sec_parameters_base_size {α γ a q₀ : ℝ} {D : ℕ} (hα : 1 / 3 < α)
    (_hα' : α < 1 / 2) (hγ : 2 * α < γ) (hγ1 : γ < 1) (hD : a < γ * D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) < ((⌊(N : ℝ) ^ α⌋₊).choose 3 : ℝ) ∧
      (N : ℝ) ^ (1 - α) < ((⌊(N : ℝ) ^ α⌋₊).choose 2 : ℝ) ∧
      q₀ < (N : ℝ) ^ α ∧
      (∃ k : ℕ, Odd k ∧ 63 < k ∧ 12 * Real.logb 2 N < k ∧ (2 * k - 1 : ℝ) ≤ (N : ℝ) ^ α) ∧
      6 ≤ (N : ℝ) ^ γ ∧ ⌈(N : ℝ) ^ γ⌉₊ < N ∧ 2 ≤ (N : ℝ) ^ (γ * D - a) := by
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ N : ℕ in atTop,
      217 ≤ (N : ℝ) ^ (3 * α - 1) ∧ 6 ≤ (N : ℝ) ^ α ∧ q₀ + 1 ≤ (N : ℝ) ^ α ∧
      266 ≤ (N : ℝ) ^ α ∧ Real.log N ≤ Real.log 2 / 48 * (N : ℝ) ^ α ∧
      6 ≤ (N : ℝ) ^ γ ∧ 2 ≤ (N : ℝ) ^ (1 - γ) ∧ 3 ≤ N ∧ 2 ≤ (N : ℝ) ^ (γ * D - a) := by
    filter_upwards [eventually_rpow_ge (by linarith : (0 : ℝ) < 3 * α - 1) 217,
      eventually_rpow_ge hα0 6, eventually_rpow_ge hα0 (q₀ + 1), eventually_rpow_ge hα0 266,
      eventually_log_le_rpow hα0 (by positivity : (0 : ℝ) < Real.log 2 / 48),
      eventually_rpow_ge hγ0 6, eventually_rpow_ge (by linarith : (0 : ℝ) < 1 - γ) 2,
      eventually_ge_atTop 3, eventually_rpow_ge (by linarith : (0 : ℝ) < γ * D - a) 2]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hN₀ N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h8
  have hN0 : (0 : ℝ) < N := by linarith
  set P := (N : ℝ) ^ α with hP
  set m := ⌊P⌋₊
  have hPm : P < m + 1 := Nat.lt_floor_add_one P
  have hmP : (m : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hm2 : P / 2 ≤ m := by linarith
  have hm3 : 3 ≤ m := by
    have : (2 : ℝ) < m := by linarith
    exact_mod_cast (show (3 : ℝ) ≤ m by
      have := Nat.cast_lt.mp (show ((2 : ℕ) : ℝ) < m by simpa using this)
      exact_mod_cast this)
  -- Powers of `P`: `P³ = N^{3α-1} N` and `P² = N^{3α-1} N^{1-α}`.
  have hP3 : P ^ 3 = (N : ℝ) ^ (3 * α - 1) * N := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      show (N : ℝ) ^ (3 * α - 1) * N = (N : ℝ) ^ (3 * α - 1) * (N : ℝ) ^ (1 : ℝ) by
        rw [Real.rpow_one], ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hP2 : P ^ 2 = (N : ℝ) ^ (3 * α - 1) * (N : ℝ) ^ (1 - α) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hNα1 : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hN0 _
  refine ⟨?_, ?_, by linarith, ?_, h6, ?_, h9⟩
  · -- `C(m,3) ≥ m³/27 ≥ P³/216 = N^{3α-1} N / 216 > N`.
    have hc := GI.power_le_choose_mul_power hm3
    have hc' : (m : ℝ) ^ 3 ≤ (m.choose 3 : ℝ) * 27 := by exact_mod_cast hc
    have hm3' : (P / 2) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hm2 3
    nlinarith
  · -- `C(m,2) ≥ m²/4 ≥ P²/16 = N^{3α-1} N^{1-α} / 16 > N^{1-α}`.
    have hc := GI.power_le_choose_mul_power (show 2 ≤ m by omega)
    have hc' : (m : ℝ) ^ 2 ≤ (m.choose 2 : ℝ) * 4 := by exact_mod_cast hc
    have hm2' : (P / 2) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hm2 2
    nlinarith
  · -- The odd row threshold `k = 2⌈6 log₂ N⌉ + 65`.
    set l := 6 * Real.logb 2 N
    have hl0 : 0 ≤ l := by
      have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith : (1 : ℝ) ≤ N)
      linarith
    have hlP : l ≤ P / 8 := by
      simp only [l, Real.logb]
      rw [mul_div_assoc', div_le_iff₀ hl2]; linarith
    have hc1 : (⌈l⌉₊ : ℝ) < l + 1 := Nat.ceil_lt_add_one hl0
    have hc2 : l ≤ ⌈l⌉₊ := Nat.le_ceil l
    refine ⟨2 * ⌈l⌉₊ + 65, ⟨⌈l⌉₊ + 32, by ring⟩, by omega, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
  · -- `⌈N^γ⌉ < N^γ + 1 ≤ N/2 + 1 < N`, since `N^γ N^{1-γ} = N`.
    have hsplit : (N : ℝ) ^ γ * (N : ℝ) ^ (1 - γ) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    have hγN : (N : ℝ) ^ γ ≤ N / 2 := by
      have := Real.rpow_pos_of_pos hN0 γ
      nlinarith
    have hc : (⌈(N : ℝ) ^ γ⌉₊ : ℝ) < (N : ℝ) ^ γ + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le _)
    have : (⌈(N : ℝ) ^ γ⌉₊ : ℝ) < N := by linarith
    exact_mod_cast this

/-- With the example values `α = 2/5`, `γ = 9/10` of Section 7.5, any `q₀`, `a` and
`D` with `a < 9D/10`, the base size exists. -/
theorem sec_parameters_base_size_example (q₀ a : ℝ) (D : ℕ) (hD : a < 9 / 10 * D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) < ((⌊(N : ℝ) ^ (2 / 5 : ℝ)⌋₊).choose 3 : ℝ) ∧
      (N : ℝ) ^ (1 - 2 / 5 : ℝ) < ((⌊(N : ℝ) ^ (2 / 5 : ℝ)⌋₊).choose 2 : ℝ) ∧
      q₀ < (N : ℝ) ^ (2 / 5 : ℝ) ∧
      (∃ k : ℕ, Odd k ∧ 63 < k ∧ 12 * Real.logb 2 N < k ∧
        (2 * k - 1 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ)) ∧
      6 ≤ (N : ℝ) ^ (9 / 10 : ℝ) ∧ ⌈(N : ℝ) ^ (9 / 10 : ℝ)⌉₊ < N ∧
      2 ≤ (N : ℝ) ^ (9 / 10 * D - a) :=
  sec_parameters_base_size (by norm_num) (by norm_num) (by norm_num) (by norm_num) hD

end GI.Paper
