module

public import Workspace.Impl.LinObjectMatrixCompose
public import Workspace.Impl.LinObjectMatrixMath
public import Workspace.Impl.LinPolyEnvelope

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectMatrixBasisPoly : PBU (fun d W _ => linBasisCost W d) := by
  unfold linBasisCost
  norm_poly

theorem linObjectMatrixTransposePoly : PBU (fun d W _ => tmGLPTrC W d d) := by
  unfold tmGLPTrC tmGLPTrColC tmGLPColW linColumnCost linVectorAccWt
  norm_poly

noncomputable def linObjectMatrixBasisBudget (C : ℕ) : ℕ :=
  linPolyEnvelope linObjectMatrixBasisPoly (100 * (C + 1) ^ 2)
noncomputable def linObjectMatrixDiffBudget (C : ℕ) : ℕ :=
  linPolyEnvelope linFiniteDifferenceCost_poly (100 * (C + 1) ^ 2)
noncomputable def linObjectMatrixColumnBound (C : ℕ) : ℕ :=
  100 * (C + linObjectMatrixBasisBudget C + linObjectMatrixDiffBudget C + 1) ^ 2
noncomputable def linObjectMatrixColumnCost (C : ℕ) : ℕ :=
  100000000 * (linObjectMatrixColumnBound C + 2) ^ 2
noncomputable def linObjectMatrixColumnSource (C : ℕ) : ℕ := 100 * (C + 1) ^ 2
noncomputable def linObjectMatrixColumnBudget (C : ℕ) : ℕ :=
  linObjectMatrixColumnCost (linObjectMatrixColumnSource C)
noncomputable def linObjectMatrixRangeBudget (C : ℕ) : ℕ :=
  linPolyEnvelope linObjectOffsetsRangePoly C
noncomputable def linObjectMatrixMapArg (C : ℕ) : ℕ :=
  100 * (C + linObjectMatrixRangeBudget C + 1) ^ 2
noncomputable def linObjectMatrixMapBudget (C : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalMapPoly (linObjectMatrixMapArg C + linObjectMatrixColumnBudget C + 1)
noncomputable def linObjectMatrixTransposeArg (C : ℕ) : ℕ :=
  100 * (C + linObjectMatrixMapBudget C + 1) ^ 2
noncomputable def linObjectMatrixTransposeBudget (C : ℕ) : ℕ :=
  linPolyEnvelope linObjectMatrixTransposePoly (linObjectMatrixTransposeArg C + C + 1)
noncomputable def linObjectMatrixEntryBound (C : ℕ) : ℕ :=
  100 * (C + 100000 * (C + 1) ^ 2 + linObjectMatrixRangeBudget C +
    linObjectMatrixMapBudget C + linObjectMatrixTransposeBudget C + 1) ^ 2
noncomputable def linObjectMatrixCost (C : ℕ) : ℕ :=
  10000000000 * (linObjectMatrixEntryBound C + 2) ^ 2

theorem linObjectMatrixCost_poly : PBU (fun _ C _ => linObjectMatrixCost C) := by
  unfold linObjectMatrixCost linObjectMatrixEntryBound linObjectMatrixTransposeBudget linObjectMatrixTransposeArg
    linObjectMatrixMapBudget linObjectMatrixMapArg linObjectMatrixRangeBudget linObjectMatrixColumnBudget
    linObjectMatrixColumnCost linObjectMatrixColumnSource linObjectMatrixColumnBound linObjectMatrixBasisBudget linObjectMatrixDiffBudget linPolyEnvelope
  norm_poly

end GI.Impl
