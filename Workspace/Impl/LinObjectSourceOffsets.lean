module

public import Workspace.Impl.LinObjectSourceOffsetsMath

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- Collect integer residues of a shifted source relative to target pieces. -/
def linObjectSourceOffsetsF (move offsets : ℕ) : Expr :=
  .letE (.call move (mk2 (arg 4) (arg 3)))
    (.call offsets (mk4 (arg 0) (arg 1) (arg 2) (.var 1)))

def linObjectSourceOffsetsFuns (b jsci jder jmem jm : ℕ) : List Expr :=
  [linObjectSourceOffsetsF (b + 1) (b + 4)] ++ mapFuns (b + 1) (b + 85) ++
    linObjectOffsetsFuns (b + 4) jsci jder jmem jm

private theorem linObjectSourceMap_length (b f : ℕ) : (mapFuns b f).length = 3 := rfl

theorem linObjectSourceOffsetsFuns_length (b jsci jder jmem jm : ℕ) :
    (linObjectSourceOffsetsFuns b jsci jder jmem jm).length = 180 := by
  simp only [linObjectSourceOffsetsFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectSourceMap_length,linObjectOffsetsFuns_length]

structure linObjectSourceOffsetsAt (P : Program) (b jsci jder jmem jm : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectSourceOffsetsF (b + 1) (b + 4))
  move : P.HasAt (b + 1) (mapFuns (b + 1) (b + 85))
  offsets : linObjectOffsetsAt P (b + 4) jsci jder jmem jm hs hd hm hc

theorem linObjectSourceOffsetsAt_of {P : Program} {b jsci jder jmem jm : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectSourceOffsetsFuns b jsci jder jmem jm))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectSourceOffsetsAt P b jsci jder jmem jm hs hd hm hc := by
  have ho : P.HasAt (b + 4) (linObjectOffsetsFuns (b + 4) jsci jder jmem jm) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectSourceMap_length,
      Nat.add_assoc,Nat.reduceAdd] using h.right
  have hm' : P.HasAt (b + 1) (mapFuns (b + 1) (b + 85)) := by
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd] using h.left.right
  exact ⟨h.left.left.single,hm',linObjectOffsetsAt_of ho hjs hjd hjm hjc⟩

end GI.Impl
