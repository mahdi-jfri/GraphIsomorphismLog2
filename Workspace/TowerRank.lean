import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace GI

def towerRank (d : ℕ) : ℤ := if d ≤ 1 then 0 else 2 * (Nat.log 2 d : ℤ) - 1

theorem floor_log_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.log 2 a + Nat.log 2 b ≤ Nat.log 2 (a * b) := by
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (Nat.ne_of_gt ha))
    (Nat.pow_log_le_self 2 (Nat.ne_of_gt hb))

/-- A genuine split of one interval into two nontrivial factors decreases rho by one. -/
theorem tower_rank_split {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    towerRank a + towerRank b + 1 ≤ towerRank (a * b) := by
  have hp := floor_log_product (by omega : 0 < a) (by omega : 0 < b)
  have hab : ¬ a * b ≤ 1 := by nlinarith
  simp only [towerRank, if_neg (by omega : ¬a ≤ 1),
    if_neg (by omega : ¬b ≤ 1), if_neg hab]
  omega

theorem tower_rank_nonneg (d : ℕ) : 0 ≤ towerRank d := by
  by_cases hd : d ≤ 1
  · simp [towerRank, hd]
  · have hlog : 1 ≤ Nat.log 2 d :=
      Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ d by omega))
    simp only [towerRank, if_neg hd]
    omega

theorem tower_rank_mono {a b : ℕ} (hab : a ≤ b) : towerRank a ≤ towerRank b := by
  by_cases ha : a ≤ 1
  · simpa [towerRank, ha] using tower_rank_nonneg b
  · have hb : ¬ b ≤ 1 := by omega
    have hlog := Nat.log_mono_right hab (b := 2)
    simp only [towerRank, if_neg ha, if_neg hb]
    omega

end GI
