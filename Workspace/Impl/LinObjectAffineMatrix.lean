module

public import Workspace.Impl.LinObjectEvalSpec
public import Workspace.Impl.LinIntBasis
public import Workspace.Impl.LinFiniteDifference
public import Workspace.Impl.TermGlueLabPTr

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- Evaluate a basis vector and subtract the affine offset, in finite coordinates. -/
def linObjectAffineMatrixColumnF (basis eval difference : ℕ) : Expr :=
  let ctx := .get (arg 0) (.nat 0)
  let g := .get (arg 0) (.nat 1)
  let offset := .get (arg 0) (.nat 2)
  let d := .get (arg 0) (.nat 3)
  .letE (.call basis (mk3 (arg 1) linIntOneE d))
    (.letE (.call eval (mk3 ctx g (.var 1)))
      (.call difference (mk3 (.get ctx (.nat 4)) (.var 2) offset)))

/-- Collect the linear matrix by affine basis evaluations, and retain the translation. -/
def linObjectAffineMatrixF (zero eval range map transpose : ℕ) : Expr :=
  let ctx := arg 0
  let g := arg 1
  let d := .length (.get ctx (.nat 4))
  .letE (.call zero (mk2 d linIntZeroE))
    (.letE (.call eval (mk3 ctx g (.var 1)))
      (.letE (.call range d)
        (.letE (.call map (mk2 (mk4 ctx g (.var 2) d) (.var 3)))
          (.letE (.call transpose (mk2 d (.var 4))) (mk2 (.var 5) (.var 2))))))

def linObjectAffineMatrixFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  [linObjectAffineMatrixF (b + 8) (b + 51) (b + 5) (b + 2) (b + 39),
    linObjectAffineMatrixColumnF (b + 11) (b + 51) (b + 14)] ++
    mapFuns (b + 2) (b + 1) ++ rangeFuns (b + 5) ++ replicateFuns (b + 8) ++
    linBasisFuns (b + 11) ++ linFiniteDifferenceFuns (b + 14) ++ tmGLPTrFuns (b + 39) ++
    linObjectAffineEvalFuns (b + 51) jsci jder jmem jm jh

private theorem linObjectMatrixMap_length (b f : ℕ) : (mapFuns b f).length = 3 := rfl
private theorem linObjectMatrixRange_length (b : ℕ) : (rangeFuns b).length = 3 := rfl
private theorem linObjectMatrixZero_length (b : ℕ) : (replicateFuns b).length = 3 := rfl
private theorem linObjectMatrixBasis_length (b : ℕ) : (linBasisFuns b).length = 3 := rfl

theorem linObjectAffineMatrixFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectAffineMatrixFuns b jsci jder jmem jm jh).length = 397 := by
  simp only [linObjectAffineMatrixFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectMatrixMap_length,linObjectMatrixRange_length,linObjectMatrixZero_length,
    linObjectMatrixBasis_length,linFiniteDifferenceFuns_length,length_tmGLPTrFuns,
    linObjectAffineEvalFuns_length]

structure linObjectAffineMatrixAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectAffineMatrixF (b + 8) (b + 51) (b + 5) (b + 2) (b + 39))
  column : P.funs[b + 1]? = some (linObjectAffineMatrixColumnF (b + 11) (b + 51) (b + 14))
  map : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1))
  range : P.HasAt (b + 5) (rangeFuns (b + 5))
  zero : P.HasAt (b + 8) (replicateFuns (b + 8))
  basis : P.HasAt (b + 11) (linBasisFuns (b + 11))
  difference : linFiniteDifferenceAt P (b + 14)
  transpose : P.HasAt (b + 39) (tmGLPTrFuns (b + 39))
  eval : linObjectAffineEvalAt P (b + 51) jsci jder jmem jm jh hs hd hm hc

set_option maxHeartbeats 500000 in
theorem linObjectAffineMatrixAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectAffineMatrixFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectAffineMatrixAt P b jsci jder jmem jm jh hs hd hm hc := by
  have hev : P.HasAt (b + 51) (linObjectAffineEvalFuns (b + 51) jsci jder jmem jm jh) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      linObjectMatrixRange_length,linObjectMatrixZero_length,linObjectMatrixBasis_length,
      linFiniteDifferenceFuns_length,length_tmGLPTrFuns,Nat.add_assoc,Nat.reduceAdd] using h.right
  have ht : P.HasAt (b + 39) (tmGLPTrFuns (b + 39)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      linObjectMatrixRange_length,linObjectMatrixZero_length,linObjectMatrixBasis_length,
      linFiniteDifferenceFuns_length,Nat.add_assoc,Nat.reduceAdd] using h.left.right
  have hdif : P.HasAt (b + 14) (linFiniteDifferenceFuns (b + 14)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      linObjectMatrixRange_length,linObjectMatrixZero_length,linObjectMatrixBasis_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.left.right
  have hb : P.HasAt (b + 11) (linBasisFuns (b + 11)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      linObjectMatrixRange_length,linObjectMatrixZero_length,Nat.add_assoc,Nat.reduceAdd] using h.left.left.left.right
  have hz : P.HasAt (b + 8) (replicateFuns (b + 8)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      linObjectMatrixRange_length,Nat.add_assoc,Nat.reduceAdd] using h.left.left.left.left.right
  have hr : P.HasAt (b + 5) (rangeFuns (b + 5)) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectMatrixMap_length,
      Nat.add_assoc,Nat.reduceAdd] using h.left.left.left.left.left.right
  have hm' : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1)) := by
    simpa only [List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd] using h.left.left.left.left.left.left.right
  have he2 := h.left.left.left.left.left.left.left
  exact ⟨he2.get (j := 0) (by simp only [List.length_cons,List.length_nil]; omega),he2.get (j := 1) (by simp only [List.length_cons,List.length_nil]; omega),hm',hr,hz,hb,
    linFiniteDifferenceAt_of hdif,ht,linObjectAffineEvalAt_of hev hjs hjd hjm hjc⟩

end GI.Impl
