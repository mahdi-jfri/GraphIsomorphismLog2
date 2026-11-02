import Workspace.Impl.LinObjectSourceCoordinateCompose

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectSourceCoordinateOffsetBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectShiftOffsetsCost_poly hs hm hc) (100*(W+1)^2)
noncomputable def linObjectSourceCoordinateRowArg (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100*(W+linObjectSourceCoordinateOffsetBudget hs hm hc W+1)^2
noncomputable def linObjectSourceCoordinateRowBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalRowPoly (linObjectSourceCoordinateRowArg hs hm hc W)
noncomputable def linObjectSourceCoordinateReduceArg (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100*(W+linObjectSourceCoordinateRowBudget hs hm hc W+1)^2
noncomputable def linObjectSourceCoordinateReduceBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope linFiniteReduceCost_poly (linObjectSourceCoordinateReduceArg hs hm hc W)
noncomputable def linObjectSourceCoordinateSource (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100*(W+linObjectSourceCoordinateOffsetBudget hs hm hc W+linObjectSourceCoordinateRowBudget hs hm hc W+
    linObjectSourceCoordinateReduceBudget hs hm hc W+1)^2
noncomputable def linObjectSourceCoordinateCost (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100000000*(linObjectSourceCoordinateSource hs hm hc W+2)^2

theorem linObjectSourceCoordinateCost_poly (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) : PBU (fun _ W _ => linObjectSourceCoordinateCost hs hm hc W) := by
  unfold linObjectSourceCoordinateCost linObjectSourceCoordinateSource linObjectSourceCoordinateReduceBudget
    linObjectSourceCoordinateReduceArg linObjectSourceCoordinateRowBudget linObjectSourceCoordinateRowArg
    linObjectSourceCoordinateOffsetBudget linPolyEnvelope
  norm_poly

end GI.Impl
