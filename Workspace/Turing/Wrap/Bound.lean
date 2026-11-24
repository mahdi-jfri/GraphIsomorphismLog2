/-
Time-bound arithmetic and Turing machine time monotonicity.

A polynomial in `exp (C * log (n + 2) * log (d + 2))` and `n` is again bounded by
`exp (C' * log (n + 2) * log (d + 2))` for a larger constant `C'`. We also show that
`Turing.TM2OutputsInTime` is monotone in its step bound, and give two helper lemmas to combine
polynomial bounds of the form `c * B ^ k`.
-/
module

public import Workspace.Statement.Turing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace GI.Turing

/-- Increasing the time bound preserves `Turing.TM2OutputsInTime`. -/
theorem tm2OutputsInTime_mono {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (h : m ≤ m')
    (he : Nonempty (Turing.TM2OutputsInTime tm l l' m)) :
    Nonempty (Turing.TM2OutputsInTime tm l l' m') :=
  he.map fun e => ⟨e.toEvalsTo, e.steps_le_m.trans h⟩

/-- Combine a sum of two polynomial bounds in a base `B ≥ 1`. -/
theorem add_poly_le {B c₁ c₂ k₁ k₂ : ℕ} (hB : 1 ≤ B) :
    c₁ * B ^ k₁ + c₂ * B ^ k₂ ≤ (c₁ + c₂) * B ^ max k₁ k₂ := by
  have h1 : B ^ k₁ ≤ B ^ max k₁ k₂ := Nat.pow_le_pow_right hB (le_max_left k₁ k₂)
  have h2 : B ^ k₂ ≤ B ^ max k₁ k₂ := Nat.pow_le_pow_right hB (le_max_right k₁ k₂)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left c₁ h1) (Nat.mul_le_mul_left c₂ h2)

/-- Raise a polynomial bound to a power. -/
theorem pow_poly_le {B c k e : ℕ} : (c * B ^ k) ^ e = c ^ e * B ^ (k * e) := by
  rw [Nat.mul_pow, ← Nat.pow_mul]

/-- A polynomial in `T` and `n` is bounded by `exp (C' * log (n + 2) * log (d + 2))` whenever
`T ≤ exp (C * log (n + 2) * log (d + 2))`. -/
theorem poly_le_exp_degree (C : ℝ) (c k : ℕ) :
    ∃ C' : ℝ, ∀ (n d T : ℕ),
      (T : ℝ) ≤ Real.exp (C * Real.log (n + 2) * Real.log (d + 2)) →
        c * (T + n + 2) ^ k ≤ ⌊Real.exp (C' * Real.log (n + 2) * Real.log (d + 2))⌋₊ := by
  set l2 : ℝ := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hl2_sq : 0 < l2 ^ 2 := sq_pos_of_pos hl2
  set C₁ : ℝ := max C (1 / l2)
  set A : ℝ := ((c * 2 ^ k : ℕ) : ℝ)
  refine ⟨A / l2 ^ 2 + k * C₁, fun n d T hT => ?_⟩
  apply Nat.le_floor
  set L : ℝ := Real.log ((n : ℝ) + 2)
  set D : ℝ := Real.log ((d : ℝ) + 2)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hd2 : (2 : ℝ) ≤ (d : ℝ) + 2 := by linarith
  have hL : l2 ≤ L := Real.log_le_log (by norm_num) hn2
  have hD : l2 ≤ D := Real.log_le_log (by norm_num) hd2
  have hL_pos : 0 < L := lt_of_lt_of_le hl2 hL
  have hD_pos : 0 < D := lt_of_lt_of_le hl2 hD
  have hLD_pos : 0 < L * D := mul_pos hL_pos hD_pos
  have hLD_ge : l2 ^ 2 ≤ L * D := by
    rw [sq]
    exact mul_le_mul hL hD hl2.le hL_pos.le
  -- Bound `T` by `exp (C₁ * L * D)`.
  have hT' : (T : ℝ) ≤ Real.exp (C₁ * L * D) := by
    refine hT.trans (Real.exp_le_exp.mpr ?_)
    have hC : C ≤ C₁ := le_max_left _ _
    nlinarith
  -- Bound `n + 2` by `exp (C₁ * L * D)`.
  have hn' : (n : ℝ) + 2 ≤ Real.exp (C₁ * L * D) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    apply Real.exp_le_exp.mpr
    have h1 : (1 / l2) * L * D = (D / l2) * L := by ring
    have h2 : 1 ≤ D / l2 := (one_le_div hl2).mpr hD
    have h3 : L ≤ (1 / l2) * L * D := by rw [h1]; nlinarith
    have hC : 1 / l2 ≤ C₁ := le_max_right _ _
    have h4 : (1 / l2) * L * D ≤ C₁ * L * D := by nlinarith
    exact h3.trans h4
  -- Combine into `c * (T + n + 2) ^ k ≤ A * exp (k * C₁ * L * D)`.
  have hsum : (T : ℝ) + (n : ℝ) + 2 ≤ 2 * Real.exp (C₁ * L * D) := by linarith
  have hpow : ((T : ℝ) + (n : ℝ) + 2) ^ k ≤ (2 * Real.exp (C₁ * L * D)) ^ k :=
    pow_le_pow_left₀ (by positivity) hsum k
  have hpow_eq : (2 * Real.exp (C₁ * L * D)) ^ k = (2 : ℝ) ^ k * Real.exp (k * C₁ * L * D) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; ring
  have hmain : ((c * (T + n + 2) ^ k : ℕ) : ℝ) ≤ A * Real.exp (k * C₁ * L * D) := by
    have hcast : ((c * (T + n + 2) ^ k : ℕ) : ℝ) = (c : ℝ) * ((T : ℝ) + (n : ℝ) + 2) ^ k := by
      push_cast; ring
    have hA : A = (c : ℝ) * (2 : ℝ) ^ k := by simp [A]
    rw [hcast, hA, mul_assoc, ← hpow_eq]
    exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg c)
  -- Absorb the constant factor `A` into the exponent.
  have hA_le : A ≤ Real.exp (A / l2 ^ 2 * L * D) := by
    have hA_nonneg : 0 ≤ A := Nat.cast_nonneg _
    have h1 : A ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have h2 : A = A / l2 ^ 2 * l2 ^ 2 := by field_simp
    have h3 : A / l2 ^ 2 * l2 ^ 2 ≤ A / l2 ^ 2 * (L * D) :=
      mul_le_mul_of_nonneg_left hLD_ge (div_nonneg hA_nonneg hl2_sq.le)
    linarith
  calc
    ((c * (T + n + 2) ^ k : ℕ) : ℝ) ≤ A * Real.exp (k * C₁ * L * D) := hmain
    _ ≤ Real.exp (A / l2 ^ 2 * L * D) * Real.exp (k * C₁ * L * D) :=
      mul_le_mul_of_nonneg_right hA_le (Real.exp_pos _).le
    _ = Real.exp ((A / l2 ^ 2 + k * C₁) * L * D) := by
      rw [← Real.exp_add]; congr 1; ring

end GI.Turing
