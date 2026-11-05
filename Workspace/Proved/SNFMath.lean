module

public import Workspace.Proved.SNFFix

@[expose] public section

/-!
# The Smith form computed by alternation and pair steps (Smith form)

The algorithm runs `snfCount A` alternation steps (`Proved/SNFAlt.lean`) and then the `n²` pair
steps (`Proved/SNFFix.lean`). The number of alternation steps is `2 ((n + 1) s + 1)`, where `s` is
the bit length of the Hermite multiplier `K = 2 n (n T)^n + 1` (`hnfKn`), which the Hermite program
already computes. It is even, so the relation is `H = P A Q`, and it is large enough because
`|det A| ≤ n! T^n ≤ (n T)^n < K < 2^s` by Hadamard's bound `Matrix.det_le`.
-/

namespace GI.Proved

open _root_.Matrix GI.Cited GI.Impl

variable {n : ℕ}

/-- The number of alternation steps. -/
def snfCount (A : _root_.Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  2 * ((n + 1) * (Nat.bits (hnfKn A)).length + 1)

/-- The state after both phases. -/
def snfRes (A : _root_.Matrix (Fin n) (Fin n) ℤ) : SnfSt n :=
  snfFix (snfIt A (snfCount A)) (n * n)

/-- `|det A| < K`. -/
theorem snf_det_lt_K (hn : 0 < n) (A : _root_.Matrix (Fin n) (Fin n) ℤ) : |A.det| < (hnfKn A : ℤ) := by
  have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := (hnfTn A : ℤ))
    (fun i j => hnf_abs_le_Tn A i j)
  simp only [Fintype.card_fin, AbsoluteValue.abs_apply, nsmul_eq_mul] at h
  have h1 : (n.factorial : ℤ) ≤ (n : ℤ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hT : (0 : ℤ) ≤ (hnfTn A : ℤ) := by positivity
  have h2 : (n.factorial : ℤ) * (hnfTn A : ℤ) ^ n ≤ (n : ℤ) ^ n * (hnfTn A : ℤ) ^ n :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have e : ((hnfKn A : ℕ) : ℤ) = 2 * n * ((n : ℤ) * hnfTn A) ^ n + 1 := by
    simp [hnfKn, hnfPn]
  have h3 : (0 : ℤ) ≤ ((n : ℤ) * hnfTn A) ^ n := by positivity
  rw [e, mul_pow]
  rw [mul_pow] at h3
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have h4 : (n : ℤ) ^ n * (hnfTn A : ℤ) ^ n ≤ 2 * n * ((n : ℤ) ^ n * (hnfTn A : ℤ) ^ n) := by
    nlinarith
  linarith

theorem snf_det_big (hn : 0 < n) (A : _root_.Matrix (Fin n) (Fin n) ℤ) :
    |A.det| ^ (n + 1) < 2 ^ (snfCount A - 1) := by
  set s := (Nat.bits (hnfKn A)).length
  have hK : hnfKn A < 2 ^ s := by
    rw [show s = Nat.size (hnfKn A) from Nat.size_eq_bits_len _]
    exact Nat.lt_size_self _
  have h1 : |A.det| < (2 : ℤ) ^ s := lt_of_lt_of_le (snf_det_lt_K hn A) (by exact_mod_cast hK.le)
  have h2 : |A.det| ^ (n + 1) < ((2 : ℤ) ^ s) ^ (n + 1) :=
    pow_lt_pow_left₀ h1 (abs_nonneg _) (by omega)
  have h3 : ((2 : ℤ) ^ s) ^ (n + 1) ≤ 2 ^ (snfCount A - 1) := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ (by norm_num) ?_
    show s * (n + 1) ≤ 2 * ((n + 1) * s + 1) - 1
    rw [mul_comm s]
    generalize (n + 1) * s = m
    omega
  exact lt_of_lt_of_le h2 h3

/-- **The algorithm computes a Smith form with unimodular multipliers.** -/
theorem snfRes_spec (hn : 0 < n) {A : _root_.Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) :
    IsUnit (snfRes A).P.det ∧ IsUnit (snfRes A).Q.det ∧
      (snfRes A).P * A * (snfRes A).Q = (snfRes A).H ∧ IsSmithForm (snfRes A).H := by
  set t := snfCount A
  have ht : 1 ≤ t := by unfold t snfCount; omega
  obtain ⟨e, hP, hQ, hHf⟩ := snfIt_inv hn hA t
  have hX : snfX A t = A := by unfold snfX t snfCount; rw [if_pos (by omega)]
  rw [hX] at e
  have hD := snfIt_diag hn hA ht (snf_det_big hn A)
  have hpos : ∀ l, 0 < (snfIt A t).H l l := fun l => (hHf ht).2.1 l l rfl
  obtain ⟨e', hP', hQ'⟩ := snfFix_rel e hP hQ hD hpos (n * n) le_rfl
  exact ⟨hP', hQ', e'.symm, snfFix_smith hD hpos⟩

end GI.Proved
