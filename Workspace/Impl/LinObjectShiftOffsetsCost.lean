import Workspace.Impl.LinObjectShiftOffsetsCompose
import Workspace.Impl.LinObjectEvalWeights

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectShiftShiftBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalShiftPoly (100 * (W + 1))
noncomputable def linObjectShiftMapArg (W : ℕ) : ℕ := 100 * (W + 1) ^ 2
noncomputable def linObjectShiftMapBudget (W : ℕ) : ℕ :=
  linPolyEnvelope linObjectEvalMapPoly (linObjectShiftMapArg W + linObjectShiftShiftBudget W + 1)
noncomputable def linObjectShiftOffsetsArg (W : ℕ) : ℕ :=
  100 * (W + linObjectShiftMapBudget W + 1) ^ 2
noncomputable def linObjectShiftOffsetsBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectOffsetsCost_poly hs hm hc) (linObjectShiftOffsetsArg W)
noncomputable def linObjectShiftSource (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectShiftMapBudget W + linObjectShiftOffsetsBudget hs hm hc W + 1) ^ 2
noncomputable def linObjectShiftOffsetsCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (W : ℕ) : ℕ := 100000000 * (linObjectShiftSource hs hm hc W + 2) ^ 2

theorem linObjectShiftOffsetsCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) : PBU (fun _ W _ => linObjectShiftOffsetsCost hs hm hc W) := by
  unfold linObjectShiftOffsetsCost linObjectShiftSource linObjectShiftOffsetsBudget linObjectShiftOffsetsArg
    linObjectShiftMapBudget linObjectShiftMapArg linObjectShiftShiftBudget linPolyEnvelope
  norm_poly

end GI.Impl
