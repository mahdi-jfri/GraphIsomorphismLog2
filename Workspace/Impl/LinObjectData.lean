module

public import Workspace.Impl.LinObjectPieces
public import Workspace.Impl.LinAbelianCoordinates
public import Workspace.Impl.LinObjectLocalRelations
public import Workspace.Impl.LinObjectProductNormal
public import Workspace.Impl.LinObjectOffsetsAnswer

@[expose] public section

/-! Compute the abelian presentation, local relation blocks, and both
Smith coordinate systems retained by the object glue. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectDataF (pieces abel locals range product quotient : ℕ) : Expr :=
  .letE (.call pieces (mk3 (arg 0) (arg 1) (arg 3)))
    (.letE (.call abel (mk2 (arg 1) (arg 0)))
      (.letE (.call range (.arith .add
        (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1)))
        (.letE (.call range (.length (.var 2)))
          (.letE (.call locals (mk2 (mk4 (arg 0) (.var 2) (.var 3) (.var 4)) (.get (.var 1) (.nat 1))))
            (.letE (.call range (.arith .add (.length (.var 2)) (.length (.var 3))))
              (.letE (mk3 (.var 6) (.var 4) (.var 5))
                (.letE (.call product (.var 7))
                  (.letE (.call quotient (.var 7))
                    (.snoc (mk4 (.var 1) (.var 2) (.var 7) (.var 8)) (.var 9))))))))))

def linObjectDataFuns (b jsci jder jmem jo jm jh js : ℕ) : List Expr :=
  [linObjectDataF (b + 1) (b + 103) (b + 199) (b + 263) (b + 266) (b + 294)] ++
    linObjectPiecesFuns (b + 1) jsci jder jmem ++ linAbelianCoordinatesFuns (b + 103) jo jm ++
    linObjectLocalRelationsFuns (b + 199) jm ++ rangeFuns (b + 263) ++
    linObjectProductNormalFuns (b + 266) jh js ++ linObjectNormalFuns (b + 294) jh js

theorem linObjectDataFuns_length (b jsci jder jmem jo jm jh js : ℕ) :
    (linObjectDataFuns b jsci jder jmem jo jm jh js).length = 346 := by
  simp only [linObjectDataFuns, List.length_append, List.length_cons, List.length_nil,
    linObjectPiecesFuns_length, linAbelianCoordinatesFuns_length, linObjectLocalRelationsFuns_length,
    linObjectProductNormalFuns_length, linObjectNormalFuns_length]
  rfl

structure linObjectDataAt (P : Program) (b jsci jder jmem jo jm jh js : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hmem : Membership)
    (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectDataF (b + 1) (b + 103) (b + 199) (b + 263) (b + 266) (b + 294))
  pieces : linObjectPiecesAt P (b + 1) jsci jder jmem hsci hder hmem
  abel : linAbelianCoordinatesAt P (b + 103) jo jm
  locals : linObjectLocalRelationsAt P (b + 199) jm hm
  range : P.HasAt (b + 263) (rangeFuns (b + 263))
  product : linObjectProductNormalAt P (b + 266) jh js
  quotient : linObjectNormalAt P (b + 294) jh js

set_option maxHeartbeats 500000 in
theorem linObjectDataAt_of {P : Program} {b jsci jder jmem jo jm jh js : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    {hm : ConstructiveMembership} (h : P.HasAt b (linObjectDataFuns b jsci jder jmem jo jm jh js))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hmem' : P.prims[jmem]? = some (membershipPrim hmem))
    (hm' : P.prims[jm]? = some (linMembershipPrim hm)) :
    linObjectDataAt P b jsci jder jmem jo jm jh js hsci hder hmem hm := by
  have hq : P.HasAt (b + 294) (linObjectNormalFuns (b + 294) jh js) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linObjectPiecesFuns_length, linAbelianCoordinatesFuns_length, linObjectLocalRelationsFuns_length,
      linObjectProductNormalFuns_length, rangeFuns, loopFuns, Nat.add_assoc, Nat.reduceAdd] using h.right
  have hp : P.HasAt (b + 266) (linObjectProductNormalFuns (b + 266) jh js) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linObjectPiecesFuns_length, linAbelianCoordinatesFuns_length, linObjectLocalRelationsFuns_length,
      rangeFuns, loopFuns, Nat.add_assoc, Nat.reduceAdd] using h.left.right
  have hr : P.HasAt (b + 263) (rangeFuns (b + 263)) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linObjectPiecesFuns_length, linAbelianCoordinatesFuns_length, linObjectLocalRelationsFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using h.left.left.right
  have hl : P.HasAt (b + 199) (linObjectLocalRelationsFuns (b + 199) jm) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linObjectPiecesFuns_length, linAbelianCoordinatesFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using h.left.left.left.right
  have ha : P.HasAt (b + 103) (linAbelianCoordinatesFuns (b + 103) jo jm) := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      linObjectPiecesFuns_length, Nat.add_assoc, Nat.reduceAdd] using h.left.left.left.left.right
  have hc : P.HasAt (b + 1) (linObjectPiecesFuns (b + 1) jsci jder jmem) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using h.left.left.left.left.left.right
  exact ⟨h.left.left.left.left.left.left.single, linObjectPiecesAt_of hc hs hd hmem',
    linAbelianCoordinatesAt_of ha, linObjectLocalRelationsAt_of hl hm', hr,
    linObjectProductNormalAt_of hp, linObjectNormalAt_of hq⟩

end GI.Impl
