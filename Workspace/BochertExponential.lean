import Workspace.BochertIndex

namespace GI.Bochert
open Equiv Equiv.Perm MulAction

theorem two_pow_pred_le_factorial (n : ℕ) : 2 ^ (n - 1) ≤ Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => norm_num
    | succ n =>
      simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one] at ih ⊢
      rw [Nat.factorial_succ, pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul ih (show 2 ≤ n + 1 + 1 by omega)

theorem two_pow_le_index_of_isPreprimitive {α : Type*} [Fintype α] [DecidableEq α]
    {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    (halt : ¬ alternatingGroup α ≤ G) :
    2 ^ ((Nat.card α + 1) / 2 - 1) ≤ G.index :=
  (two_pow_pred_le_factorial _).trans (factorial_le_index_of_isPreprimitive hG halt)

end GI.Bochert
