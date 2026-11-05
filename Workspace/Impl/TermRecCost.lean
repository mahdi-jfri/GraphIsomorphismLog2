module

public import Workspace.Impl.TermRepsCost
public import Workspace.MulticosetBounds

@[expose] public section

/-!
# The recursion bound of Theorem A.20, in the cost form of the programs (T5)

The paragraph "The recursion bound" of Theorem A.20 says: for an absolute `C` and a fixed
polynomial `P`,
`T_ℓ(b, M) ≤ C (M + 1)³ T_{ℓ-1}(b, M) + P(b, M)`,
and the derived length `ℓ` of the solvable supplement is at most `(5/2) log₃ b + 1` (Dixon,
cited `DixonDerivedLength`; we use the weaker `5 log₃ b + 1` of `count_le_exp`).

* `tmRec_le`: unrolling the recursion, `T_ℓ ≤ (C + 1)^ℓ P`.
* `tmRec_pow_le`: `(C₀ (M + 1)³ + 1)^ℓ ≤ expLogSq (tmRecA C₀) N` when `b, M ≤ N` and
  `ℓ ≤ 5 log₃ b + 1`.
* `tmRec_cost_le`: so a recursion whose per-level overhead lies in `expLogSq a N` costs at most
  `expLogSq (a + tmRecA C₀) N`, the form `TermCosetSpec` asks for.

A program for the A.20 recursion (T5) will meet the recursive inequality with `P` its
polynomial overhead per level (the point-stabilizer and transporter calls, the `A`-orbit
pieces, the profiles and the affine glue of T6); this file turns that inequality into the
final bound.
-/

namespace GI.Impl

open GI.Algorithm

/-- **Unrolling the recursion.** -/
theorem tmRec_le {T : ℕ → ℝ} {C P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (h0 : T 0 ≤ P)
    (hs : ∀ ℓ, T (ℓ + 1) ≤ C * T ℓ + P) : ∀ ℓ, T ℓ ≤ (C + 1) ^ ℓ * P := by
  intro ℓ
  induction ℓ with
  | zero => simpa using h0
  | succ ℓ ih =>
    have h1 : (1 : ℝ) ≤ (C + 1) ^ ℓ := one_le_pow₀ (by linarith)
    calc T (ℓ + 1) ≤ C * T ℓ + P := hs ℓ
      _ ≤ C * ((C + 1) ^ ℓ * P) + (C + 1) ^ ℓ * P :=
          add_le_add (mul_le_mul_of_nonneg_left ih hC) (le_mul_of_one_le_left hP h1)
      _ = (C + 1) ^ (ℓ + 1) * P := by ring

/-- The exponent constant of the recursion with branching constant `C₀`. -/
noncomputable def tmRecA (C₀ : ℝ) : ℝ := 7 * (Real.log (2 * C₀) / Real.log 2 + 3)

/-- **The number of recursion paths is quasi-polynomial.** For `C₀ ≥ 1`, `b, M ≤ N` and depth
`ℓ ≤ 5 log₃ b + 1`, `(C₀ (M + 1)³ + 1)^ℓ ≤ expLogSq (tmRecA C₀) N`. -/
theorem tmRec_pow_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {b M N ℓ : ℕ} (hb : b ≤ N) (hM : M ≤ N)
    (hℓ : (ℓ : ℝ) ≤ 5 * Real.logb 3 b + 1) :
    (C₀ * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ ≤ expLogSq (tmRecA C₀) N := by
  set L := Real.log ((N : ℝ) + 2) with hL
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hN2
  have hL0 : 0 ≤ L := hlog2.le.trans hL2
  -- the depth
  have hd : (ℓ : ℝ) ≤ 7 * L := by
    have h1 := hℓ.trans (GI.Multicoset.depth_le b)
    have h2 : Real.log ((b : ℝ) + 2) ≤ L :=
      Real.log_le_log (by positivity) (by have : (b : ℝ) ≤ N := (by exact_mod_cast hb); linarith)
    linarith
  -- the branching
  have hpos : (0 : ℝ) < C₀ * ((M : ℝ) + 1) ^ 3 + 1 := by positivity
  have hbr : C₀ * ((M : ℝ) + 1) ^ 3 + 1 ≤ 2 * C₀ * ((N : ℝ) + 2) ^ 3 := by
    have hM1 : (M : ℝ) + 1 ≤ (N : ℝ) + 2 := by
      have : (M : ℝ) ≤ N := by exact_mod_cast hM
      linarith
    have h3 : ((M : ℝ) + 1) ^ 3 ≤ ((N : ℝ) + 2) ^ 3 := pow_le_pow_left₀ (by positivity) hM1 3
    have h4 : (1 : ℝ) ≤ ((N : ℝ) + 2) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hlogbr : Real.log (C₀ * ((M : ℝ) + 1) ^ 3 + 1) ≤ Real.log (2 * C₀) + 3 * L := by
    calc Real.log (C₀ * ((M : ℝ) + 1) ^ 3 + 1) ≤ Real.log (2 * C₀ * ((N : ℝ) + 2) ^ 3) :=
          Real.log_le_log hpos hbr
      _ = Real.log (2 * C₀) + 3 * L := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hc0 : 0 ≤ Real.log (2 * C₀) := Real.log_nonneg (by linarith)
  have hc : Real.log (2 * C₀) ≤ Real.log (2 * C₀) / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL2 hc0
  have hlb0 : 0 ≤ Real.log (C₀ * ((M : ℝ) + 1) ^ 3 + 1) :=
    Real.log_nonneg (by have : 0 ≤ C₀ * ((M : ℝ) + 1) ^ 3 := (by positivity); linarith)
  rw [← Real.exp_log (pow_pos hpos ℓ), Real.log_pow]
  unfold expLogSq tmRecA
  apply Real.exp_le_exp.2
  rw [← hL]
  calc (ℓ : ℝ) * Real.log (C₀ * ((M : ℝ) + 1) ^ 3 + 1)
      ≤ (7 * L) * (Real.log (2 * C₀) / Real.log 2 * L + 3 * L) :=
        mul_le_mul hd (by linarith) hlb0 (by positivity)
    _ = 7 * (Real.log (2 * C₀) / Real.log 2 + 3) * L ^ 2 := by ring

/-- **The recursion bound of Theorem A.20 in `expLogSq` form.** A cost `T` with
`T_{ℓ+1} ≤ C₀ (M + 1)³ T_ℓ + P`, `T_0 ≤ P` and `P ≤ expLogSq a N` satisfies
`T_ℓ ≤ expLogSq (a + tmRecA C₀) N` for every depth `ℓ ≤ 5 log₃ b + 1`, when `b, M ≤ N`. -/
theorem tmRec_cost_le {T : ℕ → ℝ} {C₀ P a : ℝ} (hC₀ : 1 ≤ C₀) (hP : 0 ≤ P) {b M N ℓ : ℕ}
    (hb : b ≤ N) (hM : M ≤ N) (hℓ : (ℓ : ℝ) ≤ 5 * Real.logb 3 b + 1)
    (h0 : T 0 ≤ P) (hs : ∀ j, T (j + 1) ≤ C₀ * ((M : ℝ) + 1) ^ 3 * T j + P)
    (hPa : P ≤ expLogSq a N) : T ℓ ≤ expLogSq (a + tmRecA C₀) N := by
  have hC : 0 ≤ C₀ * ((M : ℝ) + 1) ^ 3 := by positivity
  calc T ℓ ≤ (C₀ * ((M : ℝ) + 1) ^ 3 + 1) ^ ℓ * P := tmRec_le hC hP h0 hs ℓ
    _ ≤ expLogSq (tmRecA C₀) N * expLogSq a N :=
        mul_le_mul (tmRec_pow_le hC₀ hb hM hℓ) hPa hP (expLogSq_nonneg _ _)
    _ = expLogSq (a + tmRecA C₀) N := by rw [tm_expLogSq_mul, add_comm]

end GI.Impl
