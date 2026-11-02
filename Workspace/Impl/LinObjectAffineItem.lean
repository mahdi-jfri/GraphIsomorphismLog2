import Workspace.Impl.LinObjectMatrixActualSpec

namespace GI.Impl
open GI.Cited GI.Lang

/-- Retain the matrix and offset for a cover element and its inverse. -/
def linObjectAffineItemF (matrix inv : ℕ) : Expr :=
  .letE (.call matrix (.var 0))
    (.letE (.call inv (arg 1))
      (.letE (.call matrix (mk2 (arg 0) (.var 2)))
        (mk4 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))
          (.get (.var 3) (.nat 0)) (.get (.var 3) (.nat 1)))))

def linObjectAffineItemFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  [linObjectAffineItemF (b + 1) (b + 398)] ++
    linObjectAffineMatrixFuns (b + 1) jsci jder jmem jm jh ++ invFuns (b + 398)

private theorem linObjectItemInv_length (b : ℕ) : (invFuns b).length = 12 := rfl

theorem linObjectAffineItemFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectAffineItemFuns b jsci jder jmem jm jh).length = 410 := by
  simp only [linObjectAffineItemFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectAffineMatrixFuns_length,linObjectItemInv_length]

structure linObjectAffineItemAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectAffineItemF (b + 1) (b + 398))
  matrix : linObjectAffineMatrixAt P (b + 1) jsci jder jmem jm jh hs hd hm hc
  inv : P.HasAt (b + 398) (invFuns (b + 398))

theorem linObjectAffineItemAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectAffineItemFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectAffineItemAt P b jsci jder jmem jm jh hs hd hm hc := by
  have hi : P.HasAt (b + 398) (invFuns (b + 398)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectAffineMatrixFuns_length,
      Nat.add_assoc,Nat.reduceAdd] using h.right
  have hm' : P.HasAt (b + 1) (linObjectAffineMatrixFuns (b + 1) jsci jder jmem jm jh) := by
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd] using h.left.right
  exact ⟨h.left.left.single,linObjectAffineMatrixAt_of hm' hjs hjd hjm hjc,hi⟩

end GI.Impl
