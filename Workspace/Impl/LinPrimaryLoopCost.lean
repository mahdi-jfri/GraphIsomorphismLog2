module

public import Workspace.Impl.LinPrimaryLoopInit

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 8000

noncomputable def linPrimaryLoopStepCoefficient (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimaryStepCost_poly hm hv)).choose
noncomputable def linPrimaryLoopStepDegree (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimaryStepCost_poly hm hv)).choose_spec.choose

noncomputable def linPrimaryLoopCallBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPrimaryLoopStepCoefficient hm hv * (linPrimaryIterationWeight W + 1) ^ linPrimaryLoopStepDegree hm hv
noncomputable def linPrimaryLoopStepBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  100000000 * (W + linPrimaryAccumulatorWeight W + linPrimaryLoopCallBudget hm hv W)
noncomputable def linPrimaryLoopCost (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  100000 * (linPrimaryLoopInitBudget W + W * linPrimaryLoopStepBudget hm hv W +
    1000 * ((W + 1) * (2 * W + linPrimaryAccumulatorWeight W + 1)) + 1)

theorem linPrimaryIterationWeight_ge (W : ℕ) : W ≤ linPrimaryIterationWeight W := by
  unfold linPrimaryIterationWeight
  omega

theorem linPrimaryAccumulatorWeight_ge (W : ℕ) : 4 ≤ linPrimaryAccumulatorWeight W := by
  unfold linPrimaryAccumulatorWeight
  omega

theorem linPrimaryLoopCallBudget_bound (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {W input level : ℕ} (hi : input ≤ linPrimaryIterationWeight W) (hl : level ≤ W) :
    linPrimaryStepCost hm hv input level ≤ linPrimaryLoopCallBudget hm hv W :=
  (linPoly_source_bound (linPrimaryStepCost_poly hm hv)).choose_spec.choose_spec level input
    (linPrimaryIterationWeight W) (hl.trans (linPrimaryIterationWeight_ge W)) hi

theorem linPrimaryLoopStepBudget_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linPrimaryLoopStepBudget hm hv W) := by
  have hb : PBU (fun _ W _ => linPrimaryLoopCallBudget hm hv W) :=
    PBU.smul _ (PBU.pow (PBU.addc linPrimaryIterationWeight_poly 1) _)
  exact PBU.smul 100000000 (PBU.add (PBU.add PBU.W linPrimaryAccumulatorWeight_poly) hb)

theorem linPrimaryLoopCost_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linPrimaryLoopCost hm hv W) := by
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add linPrimaryLoopInitBudget_poly
    (PBU.mul PBU.W (linPrimaryLoopStepBudget_poly hm hv)))
    (PBU.smul 1000 (PBU.mul (PBU.addc PBU.W 1)
      (PBU.addc (PBU.add (PBU.smul 2 PBU.W) linPrimaryAccumulatorWeight_poly) 1)))) 1)

private theorem linPrimaryLoopFailureNat {S W M B : ℕ} (hs : S ≤ 4 * W + 2 * M + 11) (hM : 1 ≤ M) :
    2 * S + 20 ≤ 100000000 * (W + M + B) := by omega

private theorem linPrimaryLoopSuccessNat {S W M B cc cb w : ℕ}
    (hs : S ≤ 4 * W + 2 * M + 11) (hM : 1 ≤ M) (hc : cc ≤ 2 * S + 20)
    (hb : cb ≤ 100000 * (S + 1) + 2 * B + 1) (hw : w ≤ M) :
    cc + cb + w + 1 ≤ 100000000 * (W + M + B) := by omega

theorem linPrimaryLoop_failure_budget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W S : ℕ)
    (hs : S ≤ 4 * W + 2 * linPrimaryAccumulatorWeight W + 11) :
    2 * S + 20 ≤ linPrimaryLoopStepBudget hm hv W := by
  unfold linPrimaryLoopStepBudget
  exact linPrimaryLoopFailureNat hs ((by decide : 1 ≤ 4).trans (linPrimaryAccumulatorWeight_ge W))

theorem linPrimaryLoop_success_budget (hm : ConstructiveMembership) (hv : VectorStabilizer)
    (W S cc cb w : ℕ) (hs : S ≤ 4 * W + 2 * linPrimaryAccumulatorWeight W + 11)
    (hc : cc ≤ 2 * S + 20) (hb : cb ≤ 100000 * (S + 1) + 2 * linPrimaryLoopCallBudget hm hv W + 1)
    (hw : w ≤ linPrimaryAccumulatorWeight W) : cc + cb + w + 1 ≤ linPrimaryLoopStepBudget hm hv W := by
  unfold linPrimaryLoopStepBudget
  exact linPrimaryLoopSuccessNat hs ((by decide : 1 ≤ 4).trans (linPrimaryAccumulatorWeight_ge W)) hc hb hw

private theorem linPrimaryLoopCollectedNat {W J M I D cost : ℕ} (hJ : J ≤ W)
    (hc : cost ≤ I + I + J * D + 1000 * (J + 1) * (W + J + M + 1)) :
    cost ≤ 100000 * (I + W * D + 1000 * ((W + 1) * (2 * W + M + 1)) + 1) := by
  have hm := Nat.mul_le_mul_right D hJ
  have hf := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right hJ 1))
    (show W + J + M + 1 ≤ 2 * W + M + 1 by omega)
  have he : 1000 * (W + 1) * (2 * W + M + 1) = 1000 * ((W + 1) * (2 * W + M + 1)) := by ring
  rw [he] at hf
  omega

theorem linPrimaryLoop_collected_budget (hm : ConstructiveMembership) (hv : VectorStabilizer)
    (W J cost : ℕ) (hJ : J ≤ W)
    (hc : cost ≤ linPrimaryLoopInitBudget W + linPrimaryLoopInitBudget W +
      J * linPrimaryLoopStepBudget hm hv W +
      1000 * (J + 1) * (W + J + linPrimaryAccumulatorWeight W + 1)) :
    cost ≤ linPrimaryLoopCost hm hv W := by
  unfold linPrimaryLoopCost
  exact linPrimaryLoopCollectedNat hJ hc

end GI.Impl
