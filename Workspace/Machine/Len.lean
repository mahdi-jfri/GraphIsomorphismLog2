/-
Facts about `GI.Machine.len`, the number of binary digits of a number. Every cost bound of the
log-cost machine is a sum of such lengths, so these lemmas are used everywhere.

The main tool is `GI.Machine.len_le_iff`: `len a ≤ k` exactly when `a < 2 ^ k`. Every other
lemma here follows from it.
-/
module

public import Workspace.Machine.StatementFacts
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace GI.Machine

/-- `len a ≤ k` exactly when `a < 2 ^ k`. -/
theorem len_le_iff {a k : ℕ} : len a ≤ k ↔ a < 2 ^ k := by
  by_cases ha : a = 0
  · subst ha; simp [len_zero]
  obtain ⟨h1, h2⟩ := len_spec ha
  constructor
  · intro h
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) h)
  · intro h
    by_contra hk
    rw [not_le] at hk
    have : 2 ^ k ≤ 2 ^ (len a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem lt_two_pow_len (a : ℕ) : a < 2 ^ len a := len_le_iff.mp le_rfl

/-- `k < len a` exactly when `2 ^ k ≤ a`. -/
theorem lt_len_iff {a k : ℕ} : k < len a ↔ 2 ^ k ≤ a := by
  rw [← not_le, len_le_iff, not_lt]

theorem len_mono {a b : ℕ} (h : a ≤ b) : len a ≤ len b :=
  len_le_iff.mpr (lt_of_le_of_lt h (lt_two_pow_len b))

theorem len_monotone : Monotone len := fun _ _ h => len_mono h

@[simp] theorem len_eq_zero {a : ℕ} : len a = 0 ↔ a = 0 := by
  rw [← Nat.le_zero, len_le_iff]; simp

theorem len_pos {a : ℕ} : 0 < len a ↔ 0 < a := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, Ne, len_eq_zero]

@[simp] theorem len_one : len 1 = 1 := rfl

theorem len_le_self (a : ℕ) : len a ≤ a :=
  len_le_iff.mpr (Nat.lt_two_pow_self)

theorem len_two_pow (k : ℕ) : len (2 ^ k) = k + 1 := by
  apply le_antisymm
  · rw [len_le_iff]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [Nat.succ_le_iff, lt_len_iff]

theorem len_le_one_iff {a : ℕ} : len a ≤ 1 ↔ a ≤ 1 := by
  rw [len_le_iff]; omega

theorem len_add_le (a b : ℕ) : len (a + b) ≤ max (len a) (len b) + 1 := by
  rw [len_le_iff, pow_succ]
  have ha := lt_of_lt_of_le (lt_two_pow_len a)
    (Nat.pow_le_pow_right (by norm_num) (le_max_left (len a) (len b)))
  have hb := lt_of_lt_of_le (lt_two_pow_len b)
    (Nat.pow_le_pow_right (by norm_num) (le_max_right (len a) (len b)))
  omega

theorem len_add_le_add (a b : ℕ) : len (a + b) ≤ len a + len b + 1 :=
  le_trans (len_add_le a b) (by omega)

theorem len_succ_le (a : ℕ) : len (a + 1) ≤ len a + 1 := by
  rw [len_le_iff, pow_succ]
  have := lt_two_pow_len a
  omega

theorem len_mul_le (a b : ℕ) : len (a * b) ≤ len a + len b := by
  rw [len_le_iff, pow_add]
  exact Nat.mul_lt_mul'' (lt_two_pow_len a) (lt_two_pow_len b)

theorem len_pow_le (a k : ℕ) : len (a ^ k) ≤ k * len a + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact le_trans (len_mul_le _ _) (by omega)

theorem len_sub_le (a b : ℕ) : len (a - b) ≤ len a := len_mono (Nat.sub_le a b)

theorem len_div_le (a b : ℕ) : len (a / b) ≤ len a := len_mono (Nat.div_le_self a b)

theorem len_mod_le (a b : ℕ) : len (a % b) ≤ len a := len_mono (Nat.mod_le a b)

theorem len_ite_le_one (c : Prop) [Decidable c] : len (if c then 1 else 0) ≤ 1 := by
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- `len` in terms of `Nat.log`. -/
theorem len_eq_log_add_one {a : ℕ} (ha : a ≠ 0) : len a = Nat.log 2 a + 1 := by
  unfold len
  rw [if_neg ha, Nat.log2_eq_log_two]

theorem len_le_log_add_one (a : ℕ) : len a ≤ Nat.log 2 a + 1 := by
  by_cases ha : a = 0
  · subst ha; simp [len_zero]
  · rw [len_eq_log_add_one ha]

/-- `len a ≤ log₂ a + 1` over the reals, for `a ≥ 1`. -/
theorem len_le_logb_add_one {a : ℕ} (ha : 1 ≤ a) :
    (len a : ℝ) ≤ Real.logb 2 a + 1 := by
  rw [len_eq_log_add_one (by omega)]
  push_cast
  have h : ((Nat.log 2 a : ℕ) : ℝ) ≤ Real.logb 2 a := by exact_mod_cast Real.natLog_le_logb a 2
  linarith

/-- A lower bound: `2 ^ (len a - 1) ≤ a` for `a ≠ 0`, so `len a ≤ log₂ a + 1` is tight. -/
theorem two_pow_len_sub_one_le {a : ℕ} (ha : a ≠ 0) : 2 ^ (len a - 1) ≤ a :=
  (len_spec ha).1

/-- A polynomial bound in the length: `a + 1 ≤ 2 ^ len a`. -/
theorem succ_le_two_pow_len (a : ℕ) : a + 1 ≤ 2 ^ len a := lt_two_pow_len a

end GI.Machine
