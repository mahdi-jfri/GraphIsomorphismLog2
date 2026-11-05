module

public import Workspace.Impl.LinObjectItemSpec
public import Workspace.Impl.LinMapEncoded

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectAffineRecordsFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linObjectAffineItemFuns (b + 3) jsci jder jmem jm jh

private theorem linObjectRecordsMap_length (b f : ℕ) : (mapFuns b f).length = 3 := rfl

theorem linObjectAffineRecordsFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectAffineRecordsFuns b jsci jder jmem jm jh).length = 413 := by
  simp only [linObjectAffineRecordsFuns,List.length_append,linObjectRecordsMap_length,linObjectAffineItemFuns_length]

structure linObjectAffineRecordsAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  item : linObjectAffineItemAt P (b + 3) jsci jder jmem jm jh hs hd hm hc

theorem linObjectAffineRecordsAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectAffineRecordsFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectAffineRecordsAt P b jsci jder jmem jm jh hs hd hm hc := by
  have hi : P.HasAt (b + 3) (linObjectAffineItemFuns (b + 3) jsci jder jmem jm jh) := by
    simpa only [linObjectRecordsMap_length] using h.right
  exact ⟨h.left,linObjectAffineItemAt_of hi hjs hjd hjm hjc⟩

noncomputable def linObjectRecordsItemBudget (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectItemActualCost_poly hs hm hc hh) (100 * (W + 1) ^ 2)
noncomputable def linObjectRecordsCost (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linMapBudget W (linObjectRecordsItemBudget hs hm hc hh W)

theorem linObjectRecordsCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectRecordsCost hs hm hc hh W) := by
  unfold linObjectRecordsCost linObjectRecordsItemBudget linMapBudget linPolyEnvelope
  norm_poly

end GI.Impl
