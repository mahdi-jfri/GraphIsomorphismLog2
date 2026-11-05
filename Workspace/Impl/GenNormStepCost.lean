module

public import Workspace.Impl.GenNormStep

@[expose] public section

/-! # The complete normalization cost is polynomial and fits the general-node budget -/
namespace GI.Impl
open GI.Algorithm GI.Lang GI.Paper
open GI.Cited (Preimage PointwiseStab Membership)

/-- Substitute three polynomial arguments into a uniform polynomial bound. -/
theorem normPoly_subst {f g₁ g₂ g₃ : ℕ → ℕ → ℕ → ℕ}
    (hf : PBU f) (h₁ : PBU g₁) (h₂ : PBU g₂) (h₃ : PBU g₃) :
    PBU (fun k W B => f (g₁ k W B) (g₂ k W B) (g₃ k W B)) := by
  obtain ⟨C, D, h⟩ := hf
  refine (PBU.smul C (PBU.pow (PBU.addc (PBU.add (PBU.add h₂ h₃) h₁) 2) D)).mono ?_
  intro k W B
  exact h _ _ _

/-- Preparation is polynomial in the position degree, point degree and input weight. -/
theorem normPrepCost_poly_all (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    PBU (fun n W m => normPrepCost hp hst hm n m W) :=
  PBU.smul 100 (normGrow_iter_poly hp hst hm 15
    (PBU.addc (PBU.add (PBU.add PBU.W PBU.k) PBU.B) 100))

/-- The child map and the canonical answer combination have polynomial own cost. -/
theorem normTailCost_poly (hm : Membership) : PBU (fun n W _ => normTailCost hm n W) := by
  simp only [normTailCost, normChildB, piecesW, pieceW, combInW, combOutW, combCost, combM,
    cosetNFCost, reduceCost, memCost, ansW, groupW]
  norm_poly

/-- The full own work is uniformly polynomial. The point degree is the third argument. -/
theorem normStepCost_poly (hp : Preimage) (hst : PointwiseStab) (hm : Membership) :
    PBU (fun n W m => normStepCost hp hst hm n m W) := by
  have hpK := normPrepCost_poly_all hp hst hm
  have hpT := normPoly_subst (normTailCost_poly hm) PBU.k hpK (PBU.const 0)
  have hpA : PBU (fun n _ _ => ansW n) := by unfold ansW groupW; norm_poly
  exact PBU.addc (PBU.add (PBU.add (PBU.add PBU.W (PBU.smul 4 hpK)) hpT)
    (PBU.smul 10 hpA)) 100

/-- For polynomial input weight the normalization own cost fits `E_N`, as required by
`Rest.Req` for `Wgeneral`. The harmless `+2` in the point degree is allowed explicitly. -/
theorem normStepCost_le_expLogSq (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (a d : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ n m W N : ℕ,
      n ≤ N → m ≤ N + 2 → W ≤ a * (N + 2) ^ d →
        (normStepCost hp hst hm n m W : ℝ) ≤ expLogSq A N := by
  obtain ⟨A, hA, h⟩ := (normStepCost_poly hp hst hm).le_expLogSq a d 1
  refine ⟨A, hA, fun n m W N hn hm hW => h n W m N hn hW ?_⟩
  simp only [one_mul]
  have hL : 1 ≤ Nat.log 2 (N + 2) := Nat.le_log_of_pow_le (by norm_num) (by simp)
  exact hm.trans ((by simp : N + 2 ≤ (N + 2) ^ 1).trans
    (Nat.pow_le_pow_right (by omega) hL))

end GI.Impl
