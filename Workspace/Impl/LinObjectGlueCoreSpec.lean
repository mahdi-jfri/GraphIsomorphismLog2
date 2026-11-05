module

public import Workspace.Impl.LinObjectGlueFinish
public import Workspace.Impl.LinObjectGluePrefixStep

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

private theorem linObjectGlueCore_collect {cost A C : ℕ}
    (h : cost ≤ (A+2*C+100*(A+2*C+100)*243+5)*729) :
    cost ≤ 100*(A+2*C+100)*3486784401 := by nlinarith

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [linN : ((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [linQ : IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

include linN linQ in
set_option maxHeartbeats 600000 in
set_option maxRecDepth 3000 in
theorem linObjectGlueCore_spec_of (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn)) :
    FunAll P b I.value (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
      cost ≤ linObjectGlueCoreCost hs hm ho hc hh hn hv I.value.wt) := by
  let grow := linObjectGlueGrow hs hm ho hc hh hn hv
  let W := I.value.wt
  let C := grow^[10] W
  let A := linObjectGlueArgBudget C
  let steps := linObjectGluePrefixSteps (b+1) (b+347) (b+2779) (b+449) (b+2776) (b+683)
  let J := fun i env => linObjectGluePrefixInv I i env ∧ normEnvBound (grow^[i] W) env
  let tail := Expr.ite linObjectGlueTestPlan.expr
    (linObjectCallStepsE (linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426)) linObjectGlueOutPlan.expr) .nil
  have hle (i j : ℕ) (hi : i ≤ j) : grow^[i] W ≤ grow^[j] W :=
    linObjectInflationary_iter_le grow (linObjectGlueGrow_le hs hm ho hc hh hn hv) W hi
  have harg : ∀ fp ∈ steps,linObjectPlanBudget fp.2 C ≤ A := by
    intro fp hp
    have hm' : fp.2 ∈ linObjectGluePlans := by
      simp only [steps,linObjectGluePrefixSteps,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [linObjectGluePlans]
    exact linObjectGluePlanBudget_le _ _ hm'
  have hstep : ∀ i f p,steps[i]? = some (f,p) → ∀ env,J i env → normEnvBound C env →
      ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost => J (i+1) (env++[out]) ∧ cost ≤ C) := by
    intro i f p hp env hJ hC
    have hil : i < 6 := by
      obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
      simpa only [steps,linObjectGluePrefixSteps,List.length_cons,List.length_nil] using hi
    obtain ⟨input,hr,hcall⟩ := linObjectGluePrefixStep_spec I ho hh hn h hjo hjm hjh hjs i f p hp env hJ.1 hJ.2
    refine ⟨input,hr,hcall.wt_lt.mono fun out cost hout => ⟨⟨hout.1.1,?_⟩,?_⟩⟩
    · change normEnvBound (grow^[i+1] W) (env++[out])
      rw [Function.iterate_succ_apply']
      exact normEnvBound_snoc hJ.2 (linObjectGlueGrow_le hs hm ho hc hh hn hv _) (hout.2.le.trans hout.1.2)
    · have hcost : cost ≤ grow^[i+1] W := by simpa only [Function.iterate_succ_apply'] using hout.1.2
      exact hcost.trans (hle _ 10 (by omega))
  have htail : ∀ env,J steps.length env → normEnvBound C env → EvalAll P env tail
      (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
        cost ≤ 100*(A+2*C+100)*3^5) := by
    intro env hJ hC
    exact linObjectGlueFinish_spec I ho hh hn h hjmem hjh env hJ.1 hJ.2
  have hinit : J 0 [I.value] := by
    refine ⟨rfl,?_⟩
    intro v hv'
    simp only [List.mem_singleton] at hv'
    subst v
    exact le_rfl
  have hw : normEnvBound C [I.value] := by
    intro v hv'
    simp only [List.mem_singleton] at hv'
    subst v
    exact hle 0 10 (by decide)
  have heval := linObjectCallSteps_spec steps tail J
    (AnsC (Equiv.refl (Fin n)) · (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y))) harg hstep htail [I.value] hinit hw
  apply FunAll.intro h.entry
  rw [linObjectGlueCoreF_steps]
  refine heval.mono fun out cost hout => ⟨hout.1,?_⟩
  have hcst : cost ≤ (A+2*C+100*(A+2*C+100)*243+5)*729 := hout.2
  exact linObjectGlueCore_collect hcst

omit linN linQ in
theorem linObjectGlueCore_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn)) :
    FunAll P b I.value (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
      cost ≤ linObjectGlueCoreCost hs hm ho hc hh hn hv I.value.wt) := by
  letI := linObjectAbelian_normal I.as I.ns I.abelian
  letI := linObjectAbelian_comm I.as I.ns I.abelian
  exact linObjectGlueCore_spec_of I ho hh hn h hjmem hjo hjm hjh hjs

theorem linObjectGlueCore_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) :
    ∃ K D : ℕ,∀ W,linObjectGlueCoreCost hs hm ho hc hh hn hv W ≤ K*(W+1)^D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectGlueCoreCost_poly hs hm ho hc hh hn hv)
  exact ⟨K,D,fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
