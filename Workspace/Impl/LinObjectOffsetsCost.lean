module

public import Workspace.Impl.LinObjectOffsets

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectOffsetsAppendPoly : PBU (fun _ W _ => linAppendCost W) := by
  unfold linAppendCost
  norm_poly

theorem linObjectOffsetsRangePoly : PBU (fun n _ _ => linTabulateRangeCost n) := by
  unfold linTabulateRangeCost
  norm_poly

noncomputable def linObjectOffsetsAppendBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectOffsetsAppendPoly (100 * (W + 1))

noncomputable def linObjectOffsetsTableArg (W : ℕ) : ℕ :=
  100 * (W + linObjectOffsetsAppendBudget W + 1) ^ 2
noncomputable def linObjectOffsetsTableBudget (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectPairTableCost_poly hs hm) (linObjectOffsetsTableArg W)

noncomputable def linObjectOffsetsSliceArg (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  100 * (W + linObjectOffsetsTableBudget hs hm W + 1) ^ 2
noncomputable def linObjectOffsetsSliceBudget (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  linPolyEnvelope linSliceCost_poly (linObjectOffsetsSliceArg hs hm W)

noncomputable def linObjectOffsetsRowsArg (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  100 * (W + linObjectOffsetsSliceBudget hs hm W + 1) ^ 2
noncomputable def linObjectOffsetsRowsBudget (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectOffsetRowsCost_poly (linObjectOffsetsRowsArg hs hm W)

noncomputable def linObjectOffsetsCoordsArg (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  100 * (W + linObjectOffsetsRowsBudget hs hm W + 1) ^ 2
noncomputable def linObjectOffsetsCoordsBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linElementListCost_poly hc) (linObjectOffsetsCoordsArg hs hm W)

noncomputable def linObjectOffsetsRangeBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectOffsetsRangePoly W
noncomputable def linObjectOffsetsFlatArg (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectOffsetsCoordsBudget hs hm hc W + 2 * linObjectOffsetsRangeBudget W + 1) ^ 2
noncomputable def linObjectOffsetsFlatBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectFlattenCoordsCost_poly (linObjectOffsetsFlatArg hs hm hc W)

noncomputable def linObjectOffsetsCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100000000 * ((W + 1) ^ 2 + W + linObjectOffsetsAppendBudget W + linObjectOffsetsTableBudget hs hm W +
    linObjectOffsetsSliceBudget hs hm W + linObjectOffsetsRowsBudget hs hm W +
    linObjectOffsetsCoordsBudget hs hm hc W + linObjectOffsetsRangeBudget W +
    linObjectOffsetsFlatBudget hs hm hc W + 1)

theorem linObjectOffsetsCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) : PBU (fun _ W _ => linObjectOffsetsCost hs hm hc W) := by
  unfold linObjectOffsetsCost linObjectOffsetsFlatBudget linObjectOffsetsFlatArg
    linObjectOffsetsCoordsBudget linObjectOffsetsCoordsArg linObjectOffsetsRowsBudget linObjectOffsetsRowsArg
    linObjectOffsetsSliceBudget linObjectOffsetsSliceArg linObjectOffsetsTableBudget linObjectOffsetsTableArg
    linObjectOffsetsAppendBudget linObjectOffsetsRangeBudget linPolyEnvelope
  norm_poly

end GI.Impl
