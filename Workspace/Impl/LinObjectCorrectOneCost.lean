import Workspace.Impl.LinObjectCorrectOneCompose

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectCorrectOneShiftArg (W : ℕ) : ℕ := 100 * (W+1)^2
noncomputable def linObjectCorrectOneShiftBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectShiftOffsetsCost_poly hs hm hc) (linObjectCorrectOneShiftArg W)
noncomputable def linObjectCorrectOneLiftArg (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectCorrectOneShiftBudget hs hm hc W + 1)^2
noncomputable def linObjectCorrectOneLiftBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectLiftCost_poly hh) (linObjectCorrectOneLiftArg hs hm hc W)
noncomputable def linObjectCorrectOneSource (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectCorrectOneShiftBudget hs hm hc W +
    linObjectCorrectOneLiftBudget hs hm hc hh W + permK * (W+1)^3 + 1)^2
noncomputable def linObjectCorrectOneCost (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100000000 * (linObjectCorrectOneSource hs hm hc hh W + 2)^2

theorem linObjectCorrectOneCost_poly (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectCorrectOneCost hs hm hc hh W) := by
  unfold linObjectCorrectOneCost linObjectCorrectOneSource linObjectCorrectOneLiftBudget
    linObjectCorrectOneLiftArg linObjectCorrectOneShiftBudget linObjectCorrectOneShiftArg linPolyEnvelope
  norm_poly

end GI.Impl
