import Workspace.Impl.LinObjectDataLocal

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectDataPiecesBudget (hs : SolvableCosetIntersection) (hm : Membership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectPiecesCost_poly hs hm) (100 * (W + 1))
noncomputable def linObjectDataAbelianBudget (ho : GroupOrder) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linAbelianCoordinatesBudget_poly ho hc) (100 * (W + 1))
noncomputable def linObjectDataRangeBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectOffsetsRangePoly (100 * (W + 1) ^ 2)

noncomputable def linObjectDataLocalArg (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectDataPiecesBudget hs hm W + linObjectDataAbelianBudget ho hc W +
    2 * linObjectDataRangeBudget W + 1) ^ 2
noncomputable def linObjectDataLocalBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectLocalRelationsCost_poly hc) (linObjectDataLocalArg hs hm ho hc W)

noncomputable def linObjectDataNormalArg (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectDataLocalBudget hs hm ho hc W + 2 * linObjectDataRangeBudget W + 1) ^ 2
noncomputable def linObjectDataProductBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectProductNormalAllCost_poly hh hn) (linObjectDataNormalArg hs hm ho hc W)
noncomputable def linObjectDataQuotientBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectNormalAllCost_poly hh hn) (linObjectDataNormalArg hs hm ho hc W)

noncomputable def linObjectDataCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) (W : ℕ) : ℕ :=
  100000000 * ((W + 1) ^ 2 + W + linObjectDataPiecesBudget hs hm W + linObjectDataAbelianBudget ho hc W +
    linObjectDataRangeBudget W + linObjectDataLocalBudget hs hm ho hc W +
    linObjectDataProductBudget hs hm ho hc hh hn W + linObjectDataQuotientBudget hs hm ho hc hh hn W + 1)

theorem linObjectDataCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) :
    PBU (fun _ W _ => linObjectDataCost hs hm ho hc hh hn W) := by
  unfold linObjectDataCost linObjectDataProductBudget linObjectDataQuotientBudget linObjectDataNormalArg
    linObjectDataLocalBudget linObjectDataLocalArg linObjectDataRangeBudget linObjectDataPiecesBudget
    linObjectDataAbelianBudget linPolyEnvelope
  norm_poly

end GI.Impl
