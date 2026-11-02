import Workspace.Impl.LinObjectRecordsEncoding

namespace GI.Impl
open GI.Cited GI.Lang

/-- Build the actual action records and invoke the proved primary-filtration
and two-copy-wreath solver. Input [frame context, cover group, source, target]. -/
def linObjectAffineCallerF (slice records affine : ℕ) : Expr :=
  let group := arg 1
  let stored := .get group (.nat 1)
  .letE (.call slice (mk3 (.nat 1) (.arith .sub (.length stored) (.nat 1)) stored))
    (.letE (.call records (mk2 (arg 0) (.var 1)))
      (.call affine (.snoc (mk4 group (.get (arg 0) (.nat 4)) (.var 2) (arg 2)) (arg 3))))

def linObjectAffineCallerFuns (b jsci jder jmem jm jh jv : ℕ) : List Expr :=
  [linObjectAffineCallerF (b + 1) (b + 4) (b + 417)] ++ linSliceFuns (b + 1) ++
    linObjectAffineRecordsFuns (b + 4) jsci jder jmem jm jh ++
    linAffineTransportAllFuns (b + 417) jmem jm jv

private theorem linObjectCallerSlice_length (b : ℕ) : (linSliceFuns b).length = 3 := rfl

theorem linObjectAffineCallerFuns_length (b jsci jder jmem jm jh jv : ℕ) :
    (linObjectAffineCallerFuns b jsci jder jmem jm jh jv).length = 1428 := by
  simp only [linObjectAffineCallerFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectCallerSlice_length,linObjectAffineRecordsFuns_length,linAffineTransportAllFuns_length]

structure linObjectAffineCallerAt (P : Program) (b jsci jder jmem jm jh jv : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership)
    (hc : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linObjectAffineCallerF (b + 1) (b + 4) (b + 417))
  slice : P.HasAt (b + 1) (linSliceFuns (b + 1))
  records : linObjectAffineRecordsAt P (b + 4) jsci jder jmem jm jh hs hd hm hc
  affine : linAffineTransportAllAt P (b + 417) jmem jm jv hm hc hv

theorem linObjectAffineCallerAt_of {P : Program} {b jsci jder jmem jm jh jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : P.HasAt b (linObjectAffineCallerFuns b jsci jder jmem jm jh jv))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) :
    linObjectAffineCallerAt P b jsci jder jmem jm jh jv hs hd hm hc hv := by
  have ha : P.HasAt (b + 417) (linAffineTransportAllFuns (b + 417) jmem jm jv) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectCallerSlice_length,
      linObjectAffineRecordsFuns_length,Nat.add_assoc,Nat.reduceAdd] using h.right
  have hr : P.HasAt (b + 4) (linObjectAffineRecordsFuns (b + 4) jsci jder jmem jm jh) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectCallerSlice_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.right
  have hs' : P.HasAt (b + 1) (linSliceFuns (b + 1)) := by
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd] using h.left.left.right
  exact ⟨h.left.left.left.single,hs',linObjectAffineRecordsAt_of hr hjs hjd hjm hjc,
    linAffineTransportAllAt_of hm hc hv ha hjm hjc hjv⟩

end GI.Impl
