module

public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The numeric bound for primitive solvable groups

For a primitive solvable group of degree `n` with point stabilizer `G_a`, the chain argument in
`Workspace/Proved/SolvOrderPrimitive.lean` gives `|G_a| ≤ (n - 1)(n - 2)(n - 4) ⋯`, the product of
`n - h` over the powers `h = 2^j` with `h < n`. This is `solvB k n 1` for enough fuel `k`. Here we
prove `(n · solvB n n 1)^3 ≤ 24^{n-1}`: by direct computation for `n ≤ 64`, and from
`solvB ≤ n^{m}` with `n ≤ 2^m` for larger `n`. For `n = 4` and `n = 8` the bound is close
(`24 ≤ 24` and `1344 ≤ 1661`).
-/

namespace GI.Proved

/-- `solvB k n h = (n - h)(n - 2h)(n - 4h) ⋯`, the product over the terms `2^j h < n`, computed with
fuel `k`. -/
def solvB : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | k + 1, n, h => if n ≤ h then 1 else
      (n - h) * ((Finset.range (n + 1)).filter (fun g => h ∣ g ∧ g ∣ n ∧ h < g)).sup
        (fun g => solvB k n g)

/-- One step of `solvB`, for a chosen next term `g`. -/
theorem solvB_step {k n h g : ℕ} (hnh : ¬ n ≤ h) (hg : h ∣ g ∧ g ∣ n ∧ h < g) :
    solvB (k + 1) n h ≥ (n - h) * solvB k n g := by
  rw [solvB, if_neg hnh]
  apply Nat.mul_le_mul_left
  apply Finset.le_sup (f := fun g => solvB k n g)
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hg⟩
  have hn : 0 < n := by omega
  exact Nat.lt_succ_of_le (Nat.le_of_dvd hn hg.2.1)

/-- `solvB k n h ≤ n^m` when `n ≤ 2^m h`. -/
theorem solvB_le_pow (n : ℕ) (hn : 1 ≤ n) :
    ∀ k h m, n ≤ 2 ^ m * h → solvB k n h ≤ n ^ m := by
  intro k
  induction k with
  | zero => intro h m _; exact Nat.one_le_pow _ _ hn
  | succ k ih =>
    intro h m hm
    unfold solvB
    split_ifs with hh
    · exact Nat.one_le_pow _ _ hn
    · obtain _ | m := m
      · simp at hm; omega
      · rw [pow_succ']
        apply Nat.mul_le_mul (Nat.sub_le n h)
        apply Finset.sup_le
        intro g hg
        rw [Finset.mem_filter] at hg
        obtain ⟨-, ⟨c, rfl⟩, -, hlt⟩ := hg
        have hc : 2 ≤ c := by
          rcases c with _ | _ | c
          · simp at hlt
          · simp at hlt
          · omega
        apply ih
        calc n ≤ 2 ^ (m + 1) * h := hm
          _ = 2 ^ m * (2 * h) := by ring
          _ ≤ 2 ^ m * (h * c) := Nat.mul_le_mul_left _ (by rw [mul_comm]; exact Nat.mul_le_mul_left h hc)

theorem solv_exp_aux : ∀ L, 6 ≤ L → 3 * ((L + 1) * (L + 2)) + 4 ≤ 4 * 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h2 : 6 * (L + 2) ≤ 4 * 2 ^ L := by
      have : 2 * L + 4 ≤ 2 ^ L := by
        clear ih
        induction L, hL using Nat.le_induction with
        | base => norm_num
        | succ L _ ih2 => rw [pow_succ]; omega
      omega
    have e : 3 * ((L + 1 + 1) * (L + 1 + 2)) = 3 * ((L + 1) * (L + 2)) + 6 * (L + 2) := by ring
    rw [e, pow_succ]
    omega

theorem solv_numeric_small : ∀ n, n < 65 → 1 ≤ n → (n * solvB n n 1) ^ 3 ≤ 24 ^ (n - 1) := by
  decide

/-- **The numeric bound.** For `n ≥ 1`, `(n · solvB n n 1)^3 ≤ 24^{n-1}`. -/
theorem solv_numeric (n : ℕ) (hn : 1 ≤ n) : (n * solvB n n 1) ^ 3 ≤ 24 ^ (n - 1) := by
  by_cases hs : n < 65
  · exact solv_numeric_small n hs hn
  push Not at hs
  set L := Nat.log 2 n with hL
  have hlo : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL6 : 6 ≤ L := by
    by_contra h
    push Not at h
    have : 2 ^ (L + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB : solvB n n 1 ≤ n ^ (L + 1) := solvB_le_pow n hn n 1 (L + 1) (by rw [mul_one]; omega)
  have h1 : n * solvB n n 1 ≤ n ^ (L + 2) := by
    rw [pow_succ']; exact Nat.mul_le_mul_left n hB
  have h2 : n ^ (L + 2) ≤ 2 ^ ((L + 1) * (L + 2)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hhi.le _
  have h3 : 2 ^ (3 * ((L + 1) * (L + 2))) ≤ 2 ^ (4 * (n - 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by have := solv_exp_aux L hL6; omega)
  have h4 : 2 ^ (4 * (n - 1)) ≤ 24 ^ (n - 1) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  calc (n * solvB n n 1) ^ 3 ≤ (2 ^ ((L + 1) * (L + 2))) ^ 3 :=
        Nat.pow_le_pow_left (h1.trans h2) 3
    _ = 2 ^ (3 * ((L + 1) * (L + 2))) := by rw [← pow_mul, mul_comm]
    _ ≤ 24 ^ (n - 1) := h3.trans h4

end GI.Proved
