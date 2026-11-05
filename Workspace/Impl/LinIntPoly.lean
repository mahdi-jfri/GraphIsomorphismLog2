module

public import Workspace.Impl.LinIntSlpValid
public import Workspace.Impl.LinIntSolver
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! Uniform polynomial envelopes for the explicit integer-program costs. -/
namespace GI.Impl
open GI.Lang

set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

/-- Uniform polynomial bit cost of the signed scalar arithmetic. -/
theorem linIntBinaryCost_poly : PBU (fun _ W _ => linIntBinaryCost W) := by
  simp only [linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

/-- Uniform polynomial envelope for triangular substitution. -/
theorem linTriCost_poly : PBU linTriCost := by
  unfold linTriCost
  simp only [linTriUnitCost, linTriSize, linTriArgBudget, linTriDataBudget,
    linIntDivModCost, linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost,
    linTailCost, linTrimCost, linTrimMapCost, linVectorScaleCost, linVectorBinaryCost,
    linVectorAccWt]
  norm_poly

/-- Uniform polynomial envelope for shared SLP evaluation (weight, length, dimension). -/
theorem linSlpValueCost_poly : PBU (fun t W L => linSlpValueCost W L t) := by
  simp only [linSlpValueCost, linSlpCost, linSlpLoopStepCost, linSlpStepArg,
    linSlpTableBudget, linSlpStepCost, linVectorScaleCost, linVectorBinaryCost,
    linVectorAccWt, linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

/-- The lift also has a uniform polynomial envelope. -/
theorem linHermiteLiftCost_poly : PBU (fun r W _ => linHermiteLiftCost W r) := by
  simp only [linHermiteLiftCost, linHermiteLiftRowCost, linHermiteLiftRowArg,
    linHermiteLiftPadCost, linPadCost, linRowMulCost, linRowMulStepCost,
    linRowMulEntryWt, linRowMulDotIn, linRowMulColWt, linRowMulColIn,
    linColumnCost, linDotLoopCost, linDotStepCost, linDotProductWt, linDotAccWt,
    linVectorAccWt, linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
