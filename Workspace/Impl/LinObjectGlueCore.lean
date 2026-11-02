import Workspace.Impl.LinObjectSourceCoordinateSpec
import Workspace.Impl.LinObjectSourceCorrectSpec
import Workspace.Impl.LinObjectStabilizerSpec
import Workspace.Impl.LinObjectCallerSpec
import Workspace.Impl.LinObjectCanonicalPrime
import Workspace.Impl.LinObjectAffineCosetGroup
import Workspace.Impl.LinObjectProfileMath
import Workspace.Impl.LinAffineLeftSpec
import Workspace.Impl.LinObjectGluePlans

namespace GI.Impl
open GI.Cited GI.Lang

/-- One A.20 glue level after color normalization and compression of A. -/
def linObjectGlueCoreF (data pieces coordinate affine correct stabilizer compose zero conjugate : ℕ) : Expr :=
  .letE (.call data linObjectGlueDataPlan.expr)
    (.letE (.call pieces linObjectGluePiecesPlan.expr)
      (.letE (.call conjugate linObjectGlueConjugatePlan.expr)
        (.letE (.call coordinate linObjectGlueCoordinatePlan.expr)
          (.letE (.call zero linObjectGlueZeroPlan.expr)
            (.letE (.call affine linObjectGlueAffinePlan.expr)
              (.ite linObjectGlueTestPlan.expr
                (.letE (.call compose linObjectGlueComposePlan.expr)
                  (.letE (.call correct linObjectGlueCorrectPlan.expr)
                    (.letE (.call stabilizer linObjectGlueStabilizerPlan.expr)
                      linObjectGlueOutPlan.expr))) .nil))))))

def linObjectGlueCoreFuns (b jsci jder jmem jo jm jh js jv : ℕ) : List Expr :=
  [linObjectGlueCoreF (b+1) (b+347) (b+449) (b+683) (b+2111) (b+2426) (b+2772) (b+2776) (b+2779)] ++
    (linObjectDataFuns (b+1) jsci jder jmem jo jm jh js ++
    (linObjectPiecesFuns (b+347) jsci jder jmem ++
    (linObjectSourceCoordinateFuns (b+449) jsci jder jmem jm ++
    (linObjectAffineCallerFuns (b+683) jsci jder jmem jm jh jv ++
    (linObjectSourceCorrectFuns (b+2111) jsci jder jmem jm jh ++
    (linObjectStabilizerFuns (b+2426) jsci jder jmem jm jh ++
    (composeFuns (b+2772) ++ (replicateFuns (b+2776) ++ linAffineLeftFuns (b+2779)))))))))

private theorem linObjectGlueCompose_length (b : ℕ) : (composeFuns b).length = 4 := rfl
private theorem linObjectGlueZero_length (b : ℕ) : (replicateFuns b).length = 3 := rfl

theorem linObjectGlueCoreFuns_length (b jsci jder jmem jo jm jh js jv : ℕ) :
    (linObjectGlueCoreFuns b jsci jder jmem jo jm jh js jv).length = 2810 := by
  simp only [linObjectGlueCoreFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectDataFuns_length,linObjectPiecesFuns_length,linObjectSourceCoordinateFuns_length,
    linObjectAffineCallerFuns_length,linObjectSourceCorrectFuns_length,linObjectStabilizerFuns_length,
    linObjectGlueCompose_length,linObjectGlueZero_length,linAffineLeftFuns_length]

structure linObjectGlueCoreAt (P : Program) (b jsci jder jmem jo jm jh js jv : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership)
    (hc : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linObjectGlueCoreF (b+1) (b+347) (b+449) (b+683) (b+2111)
    (b+2426) (b+2772) (b+2776) (b+2779))
  data : linObjectDataAt P (b+1) jsci jder jmem jo jm jh js hs hd hm hc
  pieces : linObjectPiecesAt P (b+347) jsci jder jmem hs hd hm
  coordinate : linObjectSourceCoordinateAt P (b+449) jsci jder jmem jm hs hd hm hc
  affine : linObjectAffineCallerAt P (b+683) jsci jder jmem jm jh jv hs hd hm hc hv
  correct : linObjectSourceCorrectAt P (b+2111) jsci jder jmem jm jh hs hd hm hc
  stabilizer : linObjectStabilizerAt P (b+2426) jsci jder jmem jm jh hs hd hm hc
  compose : P.HasAt (b+2772) (composeFuns (b+2772))
  zero : P.HasAt (b+2776) (replicateFuns (b+2776))
  conjugate : linAffineLeftAt P (b+2779)

set_option maxRecDepth 3000 in
theorem linObjectGlueCoreAt_of {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : P.HasAt b (linObjectGlueCoreFuns b jsci jder jmem jo jm jh js jv))
    (hjsci : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjder : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) :
    linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv := by
  have h0 := h.left
  have h1 := h.right
  have h2 := h1.right
  have h3 := h2.right
  have h4 := h3.right
  have h5 := h4.right
  have h6 := h5.right
  have h7 := h6.right
  have h8 := h7.right
  simp only [List.length_cons,List.length_nil,List.length_append,linObjectDataFuns_length,
    linObjectPiecesFuns_length,linObjectSourceCoordinateFuns_length,linObjectAffineCallerFuns_length,
    linObjectSourceCorrectFuns_length,linObjectStabilizerFuns_length,linObjectGlueCompose_length,
    linObjectGlueZero_length,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h0.single,linObjectDataAt_of h1.left hjsci hjder hjmem hjm,
    linObjectPiecesAt_of h2.left hjsci hjder hjmem,
    linObjectSourceCoordinateAt_of h3.left hjsci hjder hjmem hjm,
    linObjectAffineCallerAt_of h4.left hjsci hjder hjmem hjm hjv,
    linObjectSourceCorrectAt_of h5.left hjsci hjder hjmem hjm,
    linObjectStabilizerAt_of h6.left hjsci hjder hjmem hjm,h7.left,h8.left,linAffineLeftAt_of h8.right⟩

end GI.Impl
