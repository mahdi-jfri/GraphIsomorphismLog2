import Workspace.Impl.LinObjectBasisConfig
import Workspace.Impl.LinObjectOffsetsSpec
import Workspace.Impl.LinUnimodularSolve
import Workspace.Impl.LinDenseMul
import Workspace.Impl.LinFiniteReduce

/-! Evaluate the object action in a supplied Smith coordinate frame.
The same code is used for W and W/D. The frame is retained as actual
integer matrices, not as a coordinate primitive. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectAffineEvalF (lift build inv move offsets row reduce : ℕ) : Expr :=
  let ctx := arg 0
  let A := .get ctx (.nat 0)
  let N := .get ctx (.nat 1)
  let pieces := .get ctx (.nat 2)
  let V := .get ctx (.nat 3)
  let moduli := .get ctx (.nat 4)
  let d := .length moduli
  .letE (.call lift (mk3 d V (arg 2)))
    (.letE (.call build (mk3 A pieces (.var 1)))
      (.letE (.call inv (arg 1))
        (.letE (.call move (mk2 (.var 3) (.var 2)))
          (.letE (.call offsets (mk4 A N pieces (.var 4)))
            (.letE (.call row (mk3 d (.var 5) V))
              (.call reduce (mk2 (.var 6) moduli)))))))

def linObjectAffineEvalFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  [linObjectAffineEvalF (b + 1) (b + 61) (b + 102) (b + 114) (b + 117) (b + 297) (b + 325)] ++
    linUnimodularFuns (b + 1) jh ++ linObjectBasisConfigFuns (b + 61) (b + 198) ++
    invFuns (b + 102) ++ mapFuns (b + 114) (b + 198) ++
    linObjectOffsetsFuns (b + 117) jsci jder jmem jm ++ linDenseMulFuns (b + 293) ++
    linFiniteReduceFuns (b + 325)

private theorem linObjectInverse_length (b : ℕ) : (invFuns b).length = 12 := rfl
private theorem linObjectMoveMap_length (b f : ℕ) : (mapFuns b f).length = 3 := rfl

theorem linObjectAffineEvalFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectAffineEvalFuns b jsci jder jmem jm jh).length = 346 := by
  simp only [linObjectAffineEvalFuns, List.length_append, List.length_cons, List.length_nil,
    linUnimodularFuns_length, linObjectBasisConfigFuns_length, linObjectInverse_length,
    linObjectMoveMap_length, linObjectOffsetsFuns_length, linDenseMulFuns_length, linFiniteReduceFuns_length]

structure linObjectAffineEvalAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some
    (linObjectAffineEvalF (b + 1) (b + 61) (b + 102) (b + 114) (b + 117) (b + 297) (b + 325))
  lift : linUnimodularAt P (b + 1) jh
  build : linObjectBasisConfigAt P (b + 61) (b + 198)
  inv : P.HasAt (b + 102) (invFuns (b + 102))
  move : P.HasAt (b + 114) (mapFuns (b + 114) (b + 198))
  offsets : linObjectOffsetsAt P (b + 117) jsci jder jmem jm hs hd hm hc
  dense : linDenseMulAt P (b + 293)
  reduce : P.HasAt (b + 325) (linFiniteReduceFuns (b + 325))

set_option maxHeartbeats 1000000 in
theorem linObjectAffineEvalAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectAffineEvalFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectAffineEvalAt P b jsci jder jmem jm jh hs hd hm hc := by
  have hr : P.HasAt (b + 325) (linFiniteReduceFuns (b + 325)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, linObjectBasisConfigFuns_length, linObjectInverse_length,
      linObjectMoveMap_length, linObjectOffsetsFuns_length, linDenseMulFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using h.right
  have hdense : P.HasAt (b + 293) (linDenseMulFuns (b + 293)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, linObjectBasisConfigFuns_length, linObjectInverse_length,
      linObjectMoveMap_length, linObjectOffsetsFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using h.left.right
  have hoff : P.HasAt (b + 117) (linObjectOffsetsFuns (b + 117) jsci jder jmem jm) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, linObjectBasisConfigFuns_length, linObjectInverse_length,
      linObjectMoveMap_length, Nat.add_assoc, Nat.reduceAdd] using h.left.left.right
  have hmove : P.HasAt (b + 114) (mapFuns (b + 114) (b + 198)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, linObjectBasisConfigFuns_length, linObjectInverse_length,
      Nat.add_assoc, Nat.reduceAdd] using h.left.left.left.right
  have hinv : P.HasAt (b + 102) (invFuns (b + 102)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, linObjectBasisConfigFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using h.left.left.left.left.right
  have hb : P.HasAt (b + 61) (linObjectBasisConfigFuns (b + 61) (b + 198)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linUnimodularFuns_length, Nat.add_assoc, Nat.reduceAdd] using h.left.left.left.left.left.right
  have hl : P.HasAt (b + 1) (linUnimodularFuns (b + 1) jh) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using h.left.left.left.left.left.left.right
  exact ⟨h.left.left.left.left.left.left.left.single, linUnimodularAt_of hl,
    linObjectBasisConfigAt_of hb, hinv, hmove, linObjectOffsetsAt_of hoff hjs hjd hjm hjc,
    linDenseMulAt_of hdense, hr⟩

end GI.Impl
