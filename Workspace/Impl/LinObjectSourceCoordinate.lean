import Workspace.Impl.LinObjectSourceOffsetsSpec
import Workspace.Impl.LinObjectPack5
import Workspace.Impl.LinObjectFrameMath
import Workspace.Impl.LinObjectEvalWeights

namespace GI.Impl
open GI.Cited GI.Lang

/-- Read a shifted source configuration in the stored finite Smith frame. -/
def linObjectSourceCoordinateF (offsets row reduce : ℕ) : Expr :=
  let ctx := arg 0
  let A := .get ctx (.nat 0)
  let N := .get ctx (.nat 1)
  let Ps := .get ctx (.nat 2)
  let V := .get ctx (.nat 3)
  let ms := .get ctx (.nat 4)
  .letE (.call offsets (.snoc (mk4 A N Ps (arg 1)) (arg 2)))
    (.letE (.call row (mk3 (.length ms) (.var 1) V))
      (.call reduce (mk2 (.var 2) ms)))

def linObjectSourceCoordinateFuns (b jsci jder jmem jm : ℕ) : List Expr :=
  [linObjectSourceCoordinateF (b+1) (b+185) (b+213)] ++
    linObjectSourceOffsetsFuns (b+1) jsci jder jmem jm ++ linDenseMulFuns (b+181) ++
    linFiniteReduceFuns (b+213)

theorem linObjectSourceCoordinateFuns_length (b jsci jder jmem jm : ℕ) :
    (linObjectSourceCoordinateFuns b jsci jder jmem jm).length = 234 := by
  simp only [linObjectSourceCoordinateFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectSourceOffsetsFuns_length,linDenseMulFuns_length,linFiniteReduceFuns_length]

structure linObjectSourceCoordinateAt (P : Program) (b jsci jder jmem jm : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectSourceCoordinateF (b+1) (b+185) (b+213))
  offsets : linObjectSourceOffsetsAt P (b+1) jsci jder jmem jm hs hd hm hc
  dense : linDenseMulAt P (b+181)
  reduce : P.HasAt (b+213) (linFiniteReduceFuns (b+213))

theorem linObjectSourceCoordinateAt_of {P : Program} {b jsci jder jmem jm : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectSourceCoordinateFuns b jsci jder jmem jm))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectSourceCoordinateAt P b jsci jder jmem jm hs hd hm hc := by
  have he : P.HasAt b [linObjectSourceCoordinateF (b+1) (b+185) (b+213)] := h.left.left.left
  have ho : P.HasAt (b+1) (linObjectSourceOffsetsFuns (b+1) jsci jder jmem jm) := by
    simpa only [List.length_cons,List.length_nil,Nat.add_zero] using h.left.left.right
  have hd' : P.HasAt (b+181) (linDenseMulFuns (b+181)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectSourceOffsetsFuns_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.right
  have hr : P.HasAt (b+213) (linFiniteReduceFuns (b+213)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectSourceOffsetsFuns_length,
      linDenseMulFuns_length,Nat.add_assoc,Nat.reduceAdd] using h.right
  exact ⟨he.single,linObjectSourceOffsetsAt_of ho hjs hjd hjm hjc,linDenseMulAt_of hd',hr⟩

end GI.Impl
