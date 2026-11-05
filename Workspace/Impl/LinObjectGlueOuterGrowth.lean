module

public import Workspace.Impl.LinObjectGlueRaw

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectGlueOuterPlans : List linObjectReadPlan := [linObjectGlueJoinPlan,linObjectGlueNormalizePlan,
  linObjectGlueTargetPlan,linObjectGlueSourcePlan,linObjectGlueReducePlan,linObjectGlueCorePlan]
def linObjectGlueOuterArgBudget (W : ℕ) : ℕ := (linObjectGlueOuterPlans.map (linObjectPlanBudget · W)).sum+1

theorem linObjectGlueOuterArgBudget_poly : PBU (fun _ W _ => linObjectGlueOuterArgBudget W) :=
  PBU.addc (linObjectPlanListBudget_poly linObjectGlueOuterPlans) 1

theorem linObjectGlueOuterPlanBudget_le (p : linObjectReadPlan) (W : ℕ) (hp : p ∈ linObjectGlueOuterPlans) :
    linObjectPlanBudget p W ≤ linObjectGlueOuterArgBudget W := by
  have hh : linObjectPlanBudget p W ≤ (linObjectGlueOuterPlans.map (linObjectPlanBudget · W)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact hh.trans (Nat.le_add_right _ _)

theorem linObjectGlueOuterPlan_det {P : Program} {env : List Val} {W : ℕ} (h : normEnvBound W env)
    (p : linObjectReadPlan) (hp : p ∈ linObjectGlueOuterPlans) {v : Val}
    (hv : p.value env = some v) : Det P env p.expr v (linObjectGlueOuterArgBudget W) :=
  (linObjectReadPlan_det h p hv).mono (linObjectGlueOuterPlanBudget_le p W hp)

theorem linObjectGlueReduceCost_poly (hm : Membership) : PBU (fun n _ M => reduceCost hm n M) := by
  unfold reduceCost memCost
  norm_poly

noncomputable def linObjectGlueOuterAllCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (n W M : ℕ) : ℕ :=
  linAppendCost W+linObjectNormalizeCost hm W+linSliceCost W+reduceCost hm n M+
    linObjectGlueCoreCost hs hm ho hc hh hn hv W

theorem linObjectGlueOuterAllCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (linObjectGlueOuterAllCost hs hm ho hc hh hn hv) := by
  have ha : PBU (fun _ W _ => linAppendCost W) := by unfold linAppendCost; norm_poly
  exact PBU.add (PBU.add (PBU.add (PBU.add ha (linObjectNormalizeCost_poly hm)) linSliceCost_poly)
    (linObjectGlueReduceCost_poly hm)) (linObjectGlueCoreCost_poly hs hm ho hc hh hn hv)

noncomputable def linObjectGlueOuterEnvelope (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectGlueOuterAllCost_poly hs hm ho hc hh hn hv) (linObjectGlueOuterArgBudget W+W+100)
noncomputable def linObjectGlueOuterGrow (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  100*(W+linObjectGlueOuterArgBudget W+linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W+1)^2

theorem linObjectGlueOuterGrow_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (fun _ W _ => linObjectGlueOuterGrow hs hm ho hc hh hn hv W) := by
  have ha := PBU.addc (PBU.add linObjectGlueOuterArgBudget_poly PBU.W) 100
  have he := linPoly_subst (linPolyEnvelope_poly (linObjectGlueOuterAllCost_poly hs hm ho hc hh hn hv))
    (PBU.const 0) ha (PBU.const 0)
  exact PBU.smul 100 (PBU.pow (PBU.addc (PBU.add (PBU.add PBU.W linObjectGlueOuterArgBudget_poly) he) 1) 2)

theorem linObjectGlueOuterGrow_le (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : W ≤ linObjectGlueOuterGrow hs hm ho hc hh hn hv W := by
  have hp : W+linObjectGlueOuterArgBudget W+linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W+1 ≤
      (W+linObjectGlueOuterArgBudget W+linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W+1)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectGlueOuterGrow
  omega

theorem linObjectGlueOuterGrow_bound (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) {n S M W : ℕ}
    (hnW : n ≤ W) (hS : S ≤ linObjectGlueOuterArgBudget W) (hM : M ≤ W) :
    linObjectGlueOuterAllCost hs hm ho hc hh hn hv n S M ≤ linObjectGlueOuterGrow hs hm ho hc hh hn hv W := by
  have he : linObjectGlueOuterAllCost hs hm ho hc hh hn hv n S M ≤ linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W :=
    linPolyEnvelope_bound (linObjectGlueOuterAllCost_poly hs hm ho hc hh hn hv) (by omega) (by omega) (by omega)
  have hp : W+linObjectGlueOuterArgBudget W+linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W+1 ≤
      (W+linObjectGlueOuterArgBudget W+linObjectGlueOuterEnvelope hs hm ho hc hh hn hv W+1)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectGlueOuterGrow
  omega

theorem linObjectGlueOuterIter_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (i : ℕ) :
    PBU (fun _ W _ => (linObjectGlueOuterGrow hs hm ho hc hh hn hv)^[i] W) := by
  induction i with
  | zero => exact PBU.W
  | succ i ih =>
    simpa only [Function.iterate_succ_apply'] using
      linPoly_subst (linObjectGlueOuterGrow_poly hs hm ho hc hh hn hv) (PBU.const 0) ih (PBU.const 0)

noncomputable def linObjectGlueCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  let C := (linObjectGlueOuterGrow hs hm ho hc hh hn hv)^[8] W
  100*(linObjectGlueOuterArgBudget C+2*C+100)*3^10

theorem linObjectGlueCost_poly (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) : PBU (fun _ W _ => linObjectGlueCost hs hm ho hc hh hn hv W) := by
  have hi := linObjectGlueOuterIter_poly hs hm ho hc hh hn hv 8
  have ha := linPoly_subst linObjectGlueOuterArgBudget_poly (PBU.const 0) hi (PBU.const 0)
  exact PBU.mul (PBU.smul 100 (PBU.addc (PBU.add ha (PBU.smul 2 hi)) 100)) (PBU.const (3^10))

end GI.Impl
