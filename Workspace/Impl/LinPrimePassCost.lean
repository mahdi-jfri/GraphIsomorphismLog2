import Workspace.Impl.LinPrimePassSuccess

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimePassSuccessCost_mono (hm : ConstructiveMembership) {W V : ℕ} (h : W ≤ V) :
    linPrimePassSuccessCost hm W ≤ linPrimePassSuccessCost hm V := by
  have hs := linPrimarySuccessCost_mono hm h
  have ht : linPrimePassTailBudget W ≤ linPrimePassTailBudget V := by
    unfold linPrimePassTailBudget
    gcongr
  unfold linPrimePassSuccessCost
  omega

noncomputable def linPrimePassPrepareCoefficient : ℕ :=
  (linPoly_source_bound linPrimePrepareCost_poly).choose
noncomputable def linPrimePassPrepareDegree : ℕ :=
  (linPoly_source_bound linPrimePrepareCost_poly).choose_spec.choose
noncomputable def linPrimePassPrepareBudget (W : ℕ) : ℕ :=
  linPrimePassPrepareCoefficient * (100000 * (W + 1) + 1) ^ linPrimePassPrepareDegree

noncomputable def linPrimePassLoopCoefficient (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimaryLoopCost_poly hm hv)).choose
noncomputable def linPrimePassLoopDegree (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimaryLoopCost_poly hm hv)).choose_spec.choose
noncomputable def linPrimePassLoopBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPrimePassLoopCoefficient hm hv * (linPrimePassPrepareBudget W + 1) ^ linPrimePassLoopDegree hm hv

noncomputable def linPrimePassLiftArg (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  W + linPrimePassPrepareBudget W + linPrimePassLoopBudget hm hv W
noncomputable def linPrimePassLiftBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPrimePassSuccessCost hm (linPrimePassLiftArg hm hv W)
noncomputable def linPrimePassCost (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  10000000 * (W + linPrimePassPrepareBudget W + linPrimePassLoopBudget hm hv W + linPrimePassLiftBudget hm hv W + 1)

theorem linPrimePass_prepare_bound {W input : ℕ} (h : input ≤ 100000 * (W + 1)) :
    linPrimePrepareCost input ≤ linPrimePassPrepareBudget W :=
  (linPoly_source_bound linPrimePrepareCost_poly).choose_spec.choose_spec 0 input
    (100000 * (W + 1)) (Nat.zero_le _) h

theorem linPrimePass_loop_bound (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {W input : ℕ} (h : input ≤ linPrimePassPrepareBudget W) :
    linPrimaryLoopCost hm hv input ≤ linPrimePassLoopBudget hm hv W :=
  (linPoly_source_bound (linPrimaryLoopCost_poly hm hv)).choose_spec.choose_spec 0 input
    (linPrimePassPrepareBudget W) (Nat.zero_le _) h

theorem linPrimePassCost_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linPrimePassCost hm hv W) := by
  have hp : PBU (fun _ W _ => linPrimePassPrepareBudget W) :=
    PBU.smul _ (PBU.pow (PBU.addc (PBU.smul 100000 (PBU.addc PBU.W 1)) 1) _)
  have hl : PBU (fun _ W _ => linPrimePassLoopBudget hm hv W) :=
    PBU.smul _ (PBU.pow (PBU.addc hp 1) _)
  have ha : PBU (fun _ W _ => linPrimePassLiftArg hm hv W) := PBU.add (PBU.add PBU.W hp) hl
  have ht := linPoly_subst (linPrimePassSuccessCost_poly hm) (PBU.const 0) ha (PBU.const 0)
  exact PBU.smul 10000000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hp) hl) ht) 1)

end GI.Impl
