module

public import Workspace.Impl.LinAffineCallerSmall

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

noncomputable def linAffineCallerContextBudget (W : ℕ) : ℕ := linRecenterContextCost W
noncomputable def linAffineCallerReduceBudget (hmem : Membership) (W : ℕ) : ℕ := reduceCost hmem W W
noncomputable def linAffineCallerTailBudget (hmem : Membership) (W : ℕ) : ℕ :=
  loopModK * (W ^ 2 + 1) * (3 * linAffineCallerReduceBudget hmem W + 1)
noncomputable def linAffineCallerRestrictArg (hmem : Membership) (W : ℕ) : ℕ :=
  100 * (W + linAffineCallerContextBudget W + linAffineCallerReduceBudget hmem W + 1)
noncomputable def linAffineCallerRestrictBudget (hmem : Membership) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linAffineRestrictCost hm (linAffineCallerRestrictArg hmem W)
noncomputable def linAffineCallerLoopArg (hmem : Membership) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000 * (W + linAffineCallerRestrictBudget hmem hm W + linAffineCallerDiffBudget W + 1)
noncomputable def linAffineCallerLoopCoefficient (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linMixedLoopCost_poly hm hv)).choose
noncomputable def linAffineCallerLoopDegree (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linMixedLoopCost_poly hm hv)).choose_spec.choose
noncomputable def linAffineCallerLoopBudget (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linAffineCallerLoopCoefficient hm hv * (linAffineCallerLoopArg hmem hm W + 1) ^ linAffineCallerLoopDegree hm hv
noncomputable def linAffineCallerLeftArg (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) (W : ℕ) : ℕ := 100 * (linAffineCallerLoopBudget hmem hm hv W + 1)
noncomputable def linAffineCallerLeftBudget (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) (W : ℕ) : ℕ := linAffineLeftCost (linAffineCallerLeftArg hmem hm hv W)
noncomputable def linAffineCallerMainCost (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  10000000 * (W + linAffineCallerContextBudget W + linAffineCallerDiffBudget W +
    linAffineCallerReduceBudget hmem W + linAffineCallerTailBudget hmem W +
    linAffineCallerRestrictBudget hmem hm W + linAffineCallerLoopBudget hmem hm hv W +
    linAffineCallerLeftBudget hmem hm hv W + 1)
noncomputable def linAffineCallerCost (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  10000000 * (W + linAffineCallerMainCost hmem hm hv W + linAffineCallerSmallCost W + 1)

theorem linAffineCallerReduce_bound (hmem : Membership) {W n len : ℕ} (hn : n ≤ W) (hl : len ≤ W) :
    reduceCost hmem n len ≤ linAffineCallerReduceBudget hmem W := by
  simp only [linAffineCallerReduceBudget, reduceCost, memCost]
  gcongr

theorem linAffineCallerLoop_bound (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {W input : ℕ} (h : input ≤ linAffineCallerLoopArg hmem hm W) :
    linMixedLoopCost hm hv input ≤ linAffineCallerLoopBudget hmem hm hv W :=
  (linPoly_source_bound (linMixedLoopCost_poly hm hv)).choose_spec.choose_spec 0 input
    (linAffineCallerLoopArg hmem hm W) (Nat.zero_le _) h

theorem linAffineCallerSmallCost_poly : PBU (fun _ W _ => linAffineCallerSmallCost W) := by
  have hd := linPoly_subst linFiniteDifferenceCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hz : PBU (fun _ W _ => linAffineCallerZeroBudget W) := PBU.smul 10000000 (PBU.pow (PBU.addc hd 1) 3)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add PBU.W hd) hz) 1)

set_option maxHeartbeats 1000000 in
theorem linAffineCallerMainCost_poly (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linAffineCallerMainCost hmem hm hv W) := by
  have hc : PBU (fun _ W _ => linAffineCallerContextBudget W) := linRecenterContextCost_poly
  have hd := linPoly_subst linFiniteDifferenceCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hr : PBU (fun _ W _ => linAffineCallerReduceBudget hmem W) := by
    simp only [linAffineCallerReduceBudget, reduceCost, memCost]
    norm_poly
  have ht : PBU (fun _ W _ => linAffineCallerTailBudget hmem W) :=
    PBU.mul (PBU.smul loopModK (PBU.addc (PBU.pow PBU.W 2) 1)) (PBU.addc (PBU.smul 3 hr) 1)
  have hra : PBU (fun _ W _ => linAffineCallerRestrictArg hmem W) :=
    PBU.smul 100 (PBU.addc (PBU.add (PBU.add PBU.W hc) hr) 1)
  have hreb := linPoly_subst (linAffineRestrictCost_poly hm) (PBU.const 0) hra (PBU.const 0)
  have hla : PBU (fun _ W _ => linAffineCallerLoopArg hmem hm W) :=
    PBU.smul 1000 (PBU.addc (PBU.add (PBU.add PBU.W hreb) hd) 1)
  have hl : PBU (fun _ W _ => linAffineCallerLoopBudget hmem hm hv W) :=
    PBU.smul _ (PBU.pow (PBU.addc hla 1) _)
  have hleftarg : PBU (fun _ W _ => linAffineCallerLeftArg hmem hm hv W) :=
    PBU.smul 100 (PBU.addc hl 1)
  have hleft := linPoly_subst linAffineLeftCost_poly (PBU.const 0) hleftarg (PBU.const 0)
  exact PBU.smul 10000000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.add (PBU.add (PBU.add PBU.W hc) hd) hr) ht) hreb) hl) hleft) 1)

theorem linAffineCallerCost_poly (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linAffineCallerCost hmem hm hv W) :=
  PBU.smul 10000000 (PBU.addc (PBU.add (PBU.add PBU.W
    (linAffineCallerMainCost_poly hmem hm hv)) linAffineCallerSmallCost_poly) 1)

end GI.Impl
