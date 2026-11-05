module

public import Workspace.Impl.LinObjectCommonLiftMath
public import Workspace.Impl.LinObjectSourceOffsetsSpec
public import Workspace.Impl.LinObjectPack5
public import Workspace.Lang.Lib.Perm

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

/-- Correct a cover element using the common abelian translation. -/
def linObjectSourceCorrectF (offsets lift compose : ℕ) : Expr :=
  .letE (.call offsets (.snoc (mk4 (arg 0) (arg 1) (arg 2) (arg 4)) (arg 5)))
    (.letE (.call lift (mk3 (arg 0) (arg 3) (.var 1)))
      (.ite (.isNat (.var 2)) (.nat 0)
        (.call compose (mk2 (arg 5) (.get (.var 2) (.nat 1))))))

def linObjectSourceCorrectFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  [linObjectSourceCorrectF (b + 1) (b + 181) (b + 311)] ++
    linObjectSourceOffsetsFuns (b + 1) jsci jder jmem jm ++
    linObjectLiftFuns (b + 181) jh ++ composeFuns (b + 311)

theorem linObjectSourceCorrectFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectSourceCorrectFuns b jsci jder jmem jm jh).length = 315 := by
  simp only [linObjectSourceCorrectFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectSourceOffsetsFuns_length,linObjectLiftFuns_length]
  rfl

structure linObjectSourceCorrectAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectSourceCorrectF (b + 1) (b + 181) (b + 311))
  offsets : linObjectSourceOffsetsAt P (b + 1) jsci jder jmem jm hs hd hm hc
  lift : linObjectLiftAt P (b + 181) jh
  compose : P.HasAt (b + 311) (composeFuns (b + 311))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 3000 in
theorem linObjectSourceCorrectAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectSourceCorrectFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectSourceCorrectAt P b jsci jder jmem jm jh hs hd hm hc := by
  have he : P.HasAt b [linObjectSourceCorrectF (b + 1) (b + 181) (b + 311)] := h.left.left.left
  have ho : P.HasAt (b + 1) (linObjectSourceOffsetsFuns (b + 1) jsci jder jmem jm) := by
    simpa only [List.length_cons,List.length_nil,Nat.add_zero] using h.left.left.right
  have hl : P.HasAt (b + 181) (linObjectLiftFuns (b + 181) jh) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectSourceOffsetsFuns_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.right
  have hc' : P.HasAt (b + 311) (composeFuns (b + 311)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectSourceOffsetsFuns_length,
      linObjectLiftFuns_length,Nat.add_assoc,Nat.reduceAdd] using h.right
  exact ⟨he.single,linObjectSourceOffsetsAt_of ho hjs hjd hjm hjc,linObjectLiftAt_of hl,hc'⟩

end GI.Impl
