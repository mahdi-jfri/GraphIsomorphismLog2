import Workspace.Impl.LinObjectCallerCompose

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectCallerSliceBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linSliceCost_poly (100 * (W + 1) ^ 2)
noncomputable def linObjectCallerRecordsArg (W : ℕ) : ℕ :=
  100 * (W + linObjectCallerSliceBudget W + 1) ^ 2
noncomputable def linObjectCallerRecordsBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectRecordsCost_poly hs hm hc hh) (linObjectCallerRecordsArg W)
noncomputable def linObjectCallerAffineArg (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectCallerRecordsBudget hs hm hc hh W + 1) ^ 2
noncomputable def linObjectCallerAffineBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPolyEnvelope (linAffineCallerCost_poly hm hc hv) (linObjectCallerAffineArg hs hm hc hh W)
noncomputable def linObjectCallerSource (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  100 * (W + linObjectCallerSliceBudget W + linObjectCallerRecordsBudget hs hm hc hh W +
    linObjectCallerAffineBudget hs hm hc hh hv W + 1) ^ 2
noncomputable def linObjectCallerCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  10000000000 * (linObjectCallerSource hs hm hc hh hv W + 2) ^ 2

theorem linObjectCallerCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linObjectCallerCost hs hm hc hh hv W) := by
  unfold linObjectCallerCost linObjectCallerSource linObjectCallerAffineBudget linObjectCallerAffineArg
    linObjectCallerRecordsBudget linObjectCallerRecordsArg linObjectCallerSliceBudget linPolyEnvelope
  norm_poly

end GI.Impl
