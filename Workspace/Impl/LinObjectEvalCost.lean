module

public import Workspace.Impl.LinObjectEvalCompose
public import Workspace.Impl.LinObjectMoveEval
public import Workspace.Impl.LinPolyEnvelope

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectEvalShiftPoly : PBU (fun n C m => tmRiMapShC n C m) := by
  unfold tmRiMapShC tmRiShC
  norm_poly

theorem linObjectEvalMapPoly : PBU (fun _ W C => linMapBudget W C) := by
  unfold linMapBudget
  norm_poly

theorem linObjectEvalRowPoly : PBU (fun d W _ => linRowMulCost W d d) := by
  unfold linRowMulCost linRowMulStepCost linRowMulEntryWt linRowMulDotIn linRowMulColWt
    linRowMulColIn linColumnCost linDotLoopCost linDotStepCost linDotProductWt
    linDotAccWt linVectorAccWt linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

noncomputable def linObjectEvalShiftBudget (W : ℕ) : ℕ := linPolyEnvelope linObjectEvalShiftPoly (100 * (W + 1))
noncomputable def linObjectEvalLiftArg (W : ℕ) : ℕ := 100 * (W + 1) ^ 2
noncomputable def linObjectEvalLiftBudget (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linUnimodularCost_poly hh) (linObjectEvalLiftArg W)
noncomputable def linObjectEvalBuildArg (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalLiftBudget hh W + 1) ^ 2
noncomputable def linObjectEvalBuildBudget (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectBasisConfigCost_poly (linObjectEvalBuildArg hh W + linObjectEvalShiftBudget W + 1)
noncomputable def linObjectEvalInvBudget (W : ℕ) : ℕ := invK * (W + 1) ^ 4
noncomputable def linObjectEvalMoveArg (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalInvBudget W + linObjectEvalBuildBudget hh W + 1) ^ 2
noncomputable def linObjectEvalMoveBudget (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalMapPoly (linObjectEvalMoveArg hh W + linObjectEvalShiftBudget W + 1)
noncomputable def linObjectEvalOffsetsArg (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalMoveBudget hh W + 1) ^ 2
noncomputable def linObjectEvalOffsetsBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectOffsetsCost_poly hs hm hc) (linObjectEvalOffsetsArg hh W)
noncomputable def linObjectEvalRowArg (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalOffsetsBudget hs hm hc hh W + 1) ^ 2
noncomputable def linObjectEvalRowBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalRowPoly (linObjectEvalRowArg hs hm hc hh W + W + 1)
noncomputable def linObjectEvalReduceArg (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalRowBudget hs hm hc hh W + 1) ^ 2
noncomputable def linObjectEvalReduceBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope linFiniteReduceCost_poly (linObjectEvalReduceArg hs hm hc hh W + W + 1)
noncomputable def linObjectEvalStageBound (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectEvalShiftBudget W + linObjectEvalLiftBudget hh W + linObjectEvalBuildBudget hh W +
    linObjectEvalInvBudget W + linObjectEvalMoveBudget hh W + linObjectEvalOffsetsBudget hs hm hc hh W +
    linObjectEvalRowBudget hs hm hc hh W + linObjectEvalReduceBudget hs hm hc hh W + 1)
noncomputable def linObjectEvalCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100000000 * (linObjectEvalStageBound hs hm hc hh W + 2) ^ 2

theorem linObjectEvalStage_bounds (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) :
    let C := linObjectEvalStageBound hs hm hc hh W
    100 ≤ C ∧ W ≤ C ∧ linObjectEvalShiftBudget W ≤ C ∧ linObjectEvalLiftBudget hh W ≤ C ∧
      linObjectEvalBuildBudget hh W ≤ C ∧ linObjectEvalInvBudget W ≤ C ∧ linObjectEvalMoveBudget hh W ≤ C ∧
      linObjectEvalOffsetsBudget hs hm hc hh W ≤ C ∧ linObjectEvalRowBudget hs hm hc hh W ≤ C ∧
      linObjectEvalReduceBudget hs hm hc hh W ≤ C := by
  dsimp only [linObjectEvalStageBound]
  omega

theorem linObjectEvalCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectEvalCost hs hm hc hh W) := by
  unfold linObjectEvalCost linObjectEvalStageBound linObjectEvalReduceBudget linObjectEvalReduceArg
    linObjectEvalRowBudget linObjectEvalRowArg linObjectEvalOffsetsBudget linObjectEvalOffsetsArg
    linObjectEvalMoveBudget linObjectEvalMoveArg linObjectEvalInvBudget linObjectEvalBuildBudget
    linObjectEvalBuildArg linObjectEvalLiftBudget linObjectEvalLiftArg linObjectEvalShiftBudget linPolyEnvelope
  norm_poly

end GI.Impl
