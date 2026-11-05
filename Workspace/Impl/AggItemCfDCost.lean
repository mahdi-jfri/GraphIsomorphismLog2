module

public import Workspace.Impl.AggItemCfDHit

@[expose] public section

namespace GI.Impl

open GI.Lang

/-- Compare two monomial bounds without expanding a program context. -/
theorem itCfD_cost_mono (N : ℕ) {a b i j : ℕ} (hc : a ≤ b) (he : i ≤ j) :
    a * (N + 1) ^ i ≤ b * (N + 1) ^ j :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he)

theorem itCfD_pow_shift (N A i k : ℕ) :
    (A * (N + 1) ^ i + 1) ^ k ≤ (A + 1) ^ k * (N + 1) ^ (i * k) := by
  have hp : 1 ≤ (N + 1) ^ i := Nat.one_le_pow _ _ (by omega)
  have h := Nat.pow_le_pow_left
    (show A * (N + 1) ^ i + 1 ≤ (A + 1) * (N + 1) ^ i by
      rw [Nat.add_mul, one_mul]; omega) k
  simpa only [mul_pow, ← pow_mul] using h

/-- Common budget for the readout's searches and tables. -/
def itCfDAtBudget (N : ℕ) : ℕ := 10 ^ 40 * (N + 1) ^ 8

theorem itCfD_read_budget (N : ℕ) :
    10 ^ 16 * (100 * (N + 1) ^ 2 + 1) ^ 4 ≤ itCfDAtBudget N := by
  have h := Nat.mul_le_mul_left (10 ^ 16) (itCfD_pow_shift N 100 2 4)
  calc _ ≤ 10 ^ 16 * (101 ^ 4 * (N + 1) ^ 8) := h
       _ = (10 ^ 16 * 101 ^ 4) * (N + 1) ^ 8 := by rw [Nat.mul_assoc]
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num [itCfDAtBudget])

theorem itCfD_search_budget {N q : ℕ} (hq : q ≤ N) :
    q * (2 * itCfDDomK * (100 * (N + 1) ^ 2 + 1) ^ 3) +
      loopModK * (200 * (N + 1) ^ 2 + 1) * (3 * (200 * (N + 1) ^ 2) + 3) ≤
        itCfDAtBudget N := by
  have hp : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hdom := Nat.mul_le_mul_left (2 * itCfDDomK) (itCfD_pow_shift N 100 2 3)
  have h1 := Nat.mul_le_mul (show q ≤ N + 1 by omega) hdom
  have he1 : (N + 1) * (2 * itCfDDomK * (101 ^ 3 * (N + 1) ^ 6)) =
      (2 * itCfDDomK * 101 ^ 3) * (N + 1) ^ 7 := by ring
  have h1' := (h1.trans_eq he1).trans (itCfD_cost_mono N (a := 2 * itCfDDomK * 101 ^ 3)
    (b := 2 * itCfDDomK * 101 ^ 3) le_rfl (show 7 ≤ (8 : ℕ) by norm_num))
  have h2 := st_mul3 (le_refl loopModK)
    (show 200 * (N + 1) ^ 2 + 1 ≤ 201 * (N + 1) ^ 2 by omega)
    (show 3 * (200 * (N + 1) ^ 2) + 3 ≤ 603 * (N + 1) ^ 2 by omega)
  have he2 : loopModK * (201 * (N + 1) ^ 2) * (603 * (N + 1) ^ 2) =
      (loopModK * 201 * 603) * (N + 1) ^ 4 := by ring
  have h2' := (h2.trans_eq he2).trans (itCfD_cost_mono N (a := loopModK * 201 * 603)
    (b := loopModK * 201 * 603) le_rfl (show 4 ≤ (8 : ℕ) by norm_num))
  calc _ ≤ (2 * itCfDDomK * 101 ^ 3 + loopModK * 201 * 603) * (N + 1) ^ 8 := by
        simpa only [Nat.add_mul] using Nat.add_le_add h1' h2'
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num [itCfDAtBudget, itCfDDomK, loopModK])

end GI.Impl
