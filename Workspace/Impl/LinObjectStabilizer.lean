import Workspace.Impl.LinObjectAdjoinSpec
import Workspace.Impl.LinObjectKernelSpec

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectStabilizerF (correct kernel adjoin : ℕ) : Expr :=
  .letE (.call correct (mk2 (arg 0) (arg 2)))
    (.letE (.call kernel (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
      (.call adjoin (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.var 1) (.var 2))))

def linObjectStabilizerFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  [linObjectStabilizerF (b+1) (b+320) (b+330)] ++
    linObjectCorrectMapFuns (b+1) jsci jder jmem jm jh ++
    linObjectKernelFuns (b+320) jsci ++ linObjectAdjoinFuns (b+330) jmem

theorem linObjectStabilizerFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectStabilizerFuns b jsci jder jmem jm jh).length = 346 := by
  simp only [linObjectStabilizerFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectCorrectMapFuns_length,linObjectKernelFuns_length,linObjectAdjoinFuns_length]

structure linObjectStabilizerAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectStabilizerF (b+1) (b+320) (b+330))
  correct : linObjectCorrectMapAt P (b+1) jsci jder jmem jm jh hs hd hm hc
  kernel : linObjectKernelAt P (b+320) jsci hs
  adjoin : linObjectAdjoinAt P (b+330) jmem

theorem linObjectStabilizerAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectStabilizerFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectStabilizerAt P b jsci jder jmem jm jh hs hd hm hc := by
  have he : P.HasAt b [linObjectStabilizerF (b+1) (b+320) (b+330)] := h.left.left.left
  have hc' : P.HasAt (b+1) (linObjectCorrectMapFuns (b+1) jsci jder jmem jm jh) := by
    simpa only [List.length_cons,List.length_nil,Nat.add_zero] using h.left.left.right
  have hk : P.HasAt (b+320) (linObjectKernelFuns (b+320) jsci) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectCorrectMapFuns_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.right
  have ha : P.HasAt (b+330) (linObjectAdjoinFuns (b+330) jmem) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectCorrectMapFuns_length,
      linObjectKernelFuns_length,Nat.add_assoc,Nat.reduceAdd] using h.right
  exact ⟨he.single,linObjectCorrectMapAt_of hc' hjs hjd hjm hjc,linObjectKernelAt_of hk hjs,
    linObjectAdjoinAt_of ha⟩

end GI.Impl
