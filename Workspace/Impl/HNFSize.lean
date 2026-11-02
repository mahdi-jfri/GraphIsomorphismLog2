import Workspace.Impl.HNFPrep

/-!
# Sizes of the numbers of the Hermite program

Let `W ≥ r ≥ c` and let every entry of `A` be below `2^W` in absolute value. Then every number the
program computes is below `2^L` with `L = 10 (W + 1)^2`:

* `T = 1 + Σ |A i j| ≤ 2^(3W)`, since the sum has at most `W²` terms below `2^W`;
* `(r T)^r ≤ 2^(4W²)`, so `K = 2 r (r T)^r + 1 ≤ 2^(4W² + W + 2)`;
* `|d| ≤ c! T^c ≤ 2^(4W²)` (`c! ≤ c^c`), so `m = |d| K ≤ 2^(8W² + W + 2)`;
* the bound `(c+1)! T^(c+1) ≤ 2^(4W(W+1))` needed by Bareiss elimination.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

variable {r c : ℕ}

/-- The bit bound `L = 10 (W + 1)^2`. -/
def hnfL (W : ℕ) : ℕ := 10 * (W + 1) ^ 2

theorem hnf_pow_le_two_pow {a e n N : ℕ} (ha : a ≤ 2 ^ e) (hn : n ≤ N) : a ^ n ≤ 2 ^ (e * N) := by
  calc a ^ n ≤ (2 ^ e) ^ n := Nat.pow_le_pow_left ha n
    _ ≤ (2 ^ e) ^ N := Nat.pow_le_pow_right (Nat.one_le_two_pow) hn
    _ = 2 ^ (e * N) := (pow_mul 2 e N).symm

theorem hnf_lt_two_pow_of_le {x W : ℕ} (h : x ≤ W) : x < 2 ^ W :=
  lt_of_le_of_lt h Nat.lt_two_pow_self

/-- `T ≤ 2^(3W)`. -/
theorem hnfTn_le (A : Matrix (Fin r) (Fin c) ℤ) {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r)
    (hAW : ∀ i j, (A i j).natAbs < 2 ^ W) : hnfTn A ≤ 2 ^ (3 * W) := by
  have hS := hnfAbsTot_le A (B := 2 ^ W) (fun i j => (hAW i j).le) r
  have h1 : r < 2 ^ W := hnf_lt_two_pow_of_le hrW
  have h2 : c * 2 ^ W ≤ 2 ^ W * 2 ^ W :=
    Nat.mul_le_mul_right _ (hnf_lt_two_pow_of_le (hcr.trans hrW)).le
  have h3 : r * (c * 2 ^ W) < 2 ^ W * (2 ^ W * 2 ^ W) := by
    rcases Nat.eq_zero_or_pos (c * 2 ^ W) with h0 | h0
    · rw [h0, Nat.mul_zero]; positivity
    · exact Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
  have e : 2 ^ W * (2 ^ W * 2 ^ W) = 2 ^ (3 * W) := by ring
  unfold hnfTn
  omega

theorem hnfPn_le (A : Matrix (Fin r) (Fin c) ℤ) {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r)
    (hAW : ∀ i j, (A i j).natAbs < 2 ^ W) : hnfPn A ≤ 2 ^ (4 * W * W) := by
  have hT := hnfTn_le A hrW hcr hAW
  have h1 : r * hnfTn A ≤ 2 ^ (4 * W) := by
    calc r * hnfTn A ≤ 2 ^ W * 2 ^ (3 * W) :=
          Nat.mul_le_mul (hnf_lt_two_pow_of_le hrW).le hT
      _ = 2 ^ (4 * W) := by rw [← pow_add]; ring_nf
  exact hnf_pow_le_two_pow h1 hrW

theorem hnfKn_le (A : Matrix (Fin r) (Fin c) ℤ) {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r)
    (hAW : ∀ i j, (A i j).natAbs < 2 ^ W) : hnfKn A ≤ 2 ^ (4 * W * W + W + 2) := by
  have hP := hnfPn_le A hrW hcr hAW
  have h1 : 2 * r * hnfPn A ≤ 2 * 2 ^ W * 2 ^ (4 * W * W) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (hnf_lt_two_pow_of_le hrW).le) hP
  have e : 2 ^ (4 * W * W + W + 2) = 2 * (2 * 2 ^ W * 2 ^ (4 * W * W)) := by
    rw [pow_add, pow_add]; ring
  have h2 : 1 ≤ 2 * 2 ^ W * 2 ^ (4 * W * W) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold hnfKn
  omega

/-- `c! T^c ≤ 2^(4W²)`. -/
theorem hnf_fact_T_le (A : Matrix (Fin r) (Fin c) ℤ) {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r)
    (hAW : ∀ i j, (A i j).natAbs < 2 ^ W) (n : ℕ) (hn : n ≤ W) :
    n.factorial * hnfTn A ^ n ≤ 2 ^ (4 * W * W) := by
  have h1 : n.factorial ≤ 2 ^ (W * W) :=
    (Nat.factorial_le_pow n).trans (hnf_pow_le_two_pow (hnf_lt_two_pow_of_le hn).le hn)
  have h2 : hnfTn A ^ n ≤ 2 ^ (3 * W * W) := hnf_pow_le_two_pow (hnfTn_le A hrW hcr hAW) hn
  calc n.factorial * hnfTn A ^ n ≤ 2 ^ (W * W) * 2 ^ (3 * W * W) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (4 * W * W) := by rw [← pow_add]; ring_nf

theorem hnf_L_facts (W : ℕ) :
    4 * W * W + W + 2 < hnfL W ∧ 4 * W * W + (4 * W * W + W + 2) < hnfL W ∧
      4 * (W + 1) * (W + 1) < hnfL W := by
  unfold hnfL
  constructor <;> [skip; constructor] <;> nlinarith

/-- **The sizes.** -/
theorem hnf_sizes (A : Matrix (Fin r) (Fin c) ℤ) {W : ℕ} (hrW : r ≤ W) (hcr : c ≤ r)
    (hAW : ∀ i j, (A i j).natAbs < 2 ^ W) {d : ℤ} (hd : |d| ≤ c.factorial * (hnfTn A : ℤ) ^ c) :
    hnfKn A < 2 ^ hnfL W ∧ hnfMn A d < 2 ^ hnfL W ∧
      ((c + 1).factorial : ℤ) * (hnfTn A : ℤ) ^ (c + 1) < 2 ^ hnfL W := by
  obtain ⟨l1, l2, l3⟩ := hnf_L_facts W
  have hK := hnfKn_le A hrW hcr hAW
  have hd' : d.natAbs ≤ c.factorial * hnfTn A ^ c := by
    have : (d.natAbs : ℤ) ≤ c.factorial * (hnfTn A : ℤ) ^ c := by rwa [Int.natCast_natAbs]
    exact_mod_cast this
  have hdW := hd'.trans (hnf_fact_T_le A hrW hcr hAW c (hcr.trans hrW))
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hK (Nat.pow_lt_pow_right (by decide) l1)
  · calc hnfMn A d = d.natAbs * hnfKn A := rfl
      _ ≤ 2 ^ (4 * W * W) * 2 ^ (4 * W * W + W + 2) := Nat.mul_le_mul hdW hK
      _ = 2 ^ (4 * W * W + (4 * W * W + W + 2)) := (pow_add 2 _ _).symm
      _ < 2 ^ hnfL W := Nat.pow_lt_pow_right (by decide) l2
  · have h1 := hnf_fact_T_le A (W := W + 1) (by omega) hcr
      (fun i j => lt_of_lt_of_le (hAW i j) (Nat.pow_le_pow_right (by decide) (by omega)))
      (c + 1) (by omega)
    have h2 : 2 ^ (4 * (W + 1) * (W + 1)) < 2 ^ hnfL W := Nat.pow_lt_pow_right (by decide) l3
    have h3 : (c + 1).factorial * hnfTn A ^ (c + 1) < 2 ^ hnfL W := lt_of_le_of_lt h1 h2
    exact_mod_cast h3

end GI.Impl
