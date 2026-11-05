module

public import Workspace.Impl.LinObjectGlueCore
public import Workspace.Impl.LinObjectCallSteps
public import Workspace.Impl.LinObjectNormalizeBounds

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectGlueJoinPlan : linObjectReadPlan := .list [.read 0 [4],.read 0 [3]]
def linObjectGlueNormalizePlan : linObjectReadPlan := .read 1 []
def linObjectGlueTargetPlan : linObjectReadPlan := .list [.nat 0,.length (.read 0 [4]),.read 2 []]
def linObjectGlueSourcePlan : linObjectReadPlan := .list [.length (.read 0 [4]),.length (.read 0 [3]),.read 2 []]
def linObjectGlueReducePlan : linObjectReadPlan := .read 0 [2]
def linObjectGlueCorePlan : linObjectReadPlan := .list
  [.read 0 [0],.read 0 [1],.read 5 [],.read 4 [],.read 3 [],.read 0 [5],.read 0 [6]]

def linObjectGlueF (append normalize slice reduce core : ℕ) : Expr :=
  linObjectCallStepsE [(append,linObjectGlueJoinPlan),(normalize,linObjectGlueNormalizePlan),
    (slice,linObjectGlueTargetPlan),(slice,linObjectGlueSourcePlan),(reduce,linObjectGlueReducePlan)]
    (.call core linObjectGlueCorePlan.expr)

/-- The concrete A.20 object glue list, including input normalization.
All cited indices are parameters for final primitive-table assembly. -/
def gObjF (b jsci jder jmem jo jm jh js jv : ℕ) : List Expr :=
  [linObjectGlueF (b+1) (b+4) (b+25) (b+28) (b+33)] ++
    (appendFuns (b+1) ++ (linObjectNormalizeFuns (b+4) jmem ++ (linSliceFuns (b+25) ++
    (reduceFuns (b+28) jmem ++ linObjectGlueCoreFuns (b+33) jsci jder jmem jo jm jh js jv))))

private theorem linObjectGlueAppend_length (b : ℕ) : (appendFuns b).length = 3 := rfl
private theorem linObjectGlueReduce_length (b j : ℕ) : (reduceFuns b j).length = 5 := rfl

theorem gObjF_length (b jsci jder jmem jo jm jh js jv : ℕ) :
    (gObjF b jsci jder jmem jo jm jh js jv).length = 2843 := by
  simp only [gObjF,List.length_append,List.length_cons,List.length_nil,linObjectGlueAppend_length,
    linObjectNormalizeFuns_length,linSliceFuns_length,linObjectGlueReduce_length,linObjectGlueCoreFuns_length]

structure linObjectGlueAt (P : Program) (b jsci jder jmem jo jm jh js jv : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership)
    (hc : ConstructiveMembership) (hv : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linObjectGlueF (b+1) (b+4) (b+25) (b+28) (b+33))
  append : P.HasAt (b+1) (appendFuns (b+1))
  normalize : linObjectNormalizeAt P (b+4) jmem
  slice : P.HasAt (b+25) (linSliceFuns (b+25))
  reduce : P.HasAt (b+28) (reduceFuns (b+28) jmem)
  core : linObjectGlueCoreAt P (b+33) jsci jder jmem jo jm jh js jv hs hd hm hc hv

theorem linObjectGlueAt_of {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : P.HasAt b (gObjF b jsci jder jmem jo jm jh js jv))
    (hjsci : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjder : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) :
    linObjectGlueAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv := by
  have h0 := h.left
  have h1 := h.right
  have h2 := h1.right
  have h3 := h2.right
  have h4 := h3.right
  simp only [List.length_cons,List.length_nil,linObjectGlueAppend_length,linObjectNormalizeFuns_length,
    linSliceFuns_length,linObjectGlueReduce_length,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] at h1 h2 h3 h4
  exact ⟨h0.single,h1.left,linObjectNormalizeAt_of h2.left,h3.left,h4.left,
    linObjectGlueCoreAt_of h4.right hjsci hjder hjmem hjm hjv⟩

end GI.Impl
