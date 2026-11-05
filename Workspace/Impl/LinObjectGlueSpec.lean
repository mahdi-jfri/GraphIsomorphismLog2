module

public import Workspace.Impl.LinObjectGlueOuterStep

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

private theorem linObjectGlue_collect {cost A C : ℕ}
    (h : cost ≤ (A+2*C+(A+2*C+1)+5)*243) : cost ≤ 100*(A+2*C+100)*59049 := by nlinarith

private theorem linObjectGlueOuterCore_le (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) (n W M : ℕ) :
    linObjectGlueCoreCost hs hm ho hc hh hn hv W ≤ linObjectGlueOuterAllCost hs hm ho hc hh hn hv n W M := by
  unfold linObjectGlueOuterAllCost
  omega

set_option maxHeartbeats 50000 in
set_option maxRecDepth 2500 in
theorem linObjectGlueOuterCore_spec {n : ℕ} (I : linObjectGlueRaw n)
    (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv T : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn))
    (hW : normEnvBound T I.prefixValues) :
    FunAll P (b+33) I.normalize.value (fun out cost =>
      AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
      cost ≤ linObjectGlueOuterGrow hs hm ho hc hh hn hv T) := by
  have hr : linObjectGlueCorePlan.value I.prefixValues = some I.normalize.value := rfl
  have dn := linObjectGlueOuterPlan_det (P:=P) hW linObjectGlueCorePlan (by simp [linObjectGlueOuterPlans]) hr
  have hnT : n ≤ T := I.size_bounds.1.trans (normEnvBound_get hW (slot:=0) rfl)
  have hcst := linObjectGlueOuterGrow_bound hs hm ho hc hh hn hv hnT dn.wt_lt.le (M:=0) (Nat.zero_le _)
  refine (linObjectGlueCore_spec I.normalize ho hh hn h.core hjmem hjo hjm hjh hjs).mono fun out cost hout => ⟨?_,?_⟩
  · simpa only [I.normalize_iso] using hout.1
  · have hown : cost ≤ linObjectGlueCoreCost hs hm ho hc hh hn hv I.normalize.value.wt := hout.2
    exact hown.trans ((linObjectGlueOuterCore_le hs hm ho hc hh hn hv _ _ _).trans hcst)

set_option maxHeartbeats 50000 in
set_option maxRecDepth 3000 in
theorem linObjectGlue_spec {n : ℕ} (I : linObjectGlueRaw n)
    (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn)) :
    FunAll P b I.value (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
      cost ≤ linObjectGlueCost hs hm ho hc hh hn hv I.value.wt) := by
  let grow := linObjectGlueOuterGrow hs hm ho hc hh hn hv
  let W := I.value.wt
  let C := grow^[8] W
  let A := linObjectGlueOuterArgBudget C
  let steps := linObjectGlueOuterSteps (b+1) (b+4) (b+25) (b+28)
  let J := fun i env => linObjectGlueOuterInv I i env ∧ normEnvBound (grow^[i] W) env
  have hle (i j : ℕ) (hi : i ≤ j) : grow^[i] W ≤ grow^[j] W :=
    linObjectInflationary_iter_le grow (linObjectGlueOuterGrow_le hs hm ho hc hh hn hv) W hi
  have harg : ∀ fp ∈ steps,linObjectPlanBudget fp.2 C ≤ A := by
    intro fp hp
    have hm' : fp.2 ∈ linObjectGlueOuterPlans := by
      simp only [steps,linObjectGlueOuterSteps,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [linObjectGlueOuterPlans]
    exact linObjectGlueOuterPlanBudget_le _ _ hm'
  have hstep : ∀ i f p,steps[i]? = some (f,p) → ∀ env,J i env → normEnvBound C env →
      ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost => J (i+1) (env++[out]) ∧ cost ≤ C) := by
    intro i f p hp env hJ hC
    have hil : i < 5 := by
      obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
      simpa only [steps,linObjectGlueOuterSteps,List.length_cons,List.length_nil] using hi
    obtain ⟨input,hr,hcall⟩ := linObjectGlueOuterStep_spec I ho hh hn h hjmem i f p hp env hJ.1 hJ.2
    refine ⟨input,hr,hcall.wt_lt.mono fun out cost hout => ⟨⟨hout.1.1,?_⟩,?_⟩⟩
    · change normEnvBound (grow^[i+1] W) (env++[out])
      rw [Function.iterate_succ_apply']
      exact normEnvBound_snoc hJ.2 (linObjectGlueOuterGrow_le hs hm ho hc hh hn hv _) (hout.2.le.trans hout.1.2)
    · have hcost : cost ≤ grow^[i+1] W := by simpa only [Function.iterate_succ_apply'] using hout.1.2
      exact hcost.trans (hle _ 8 (by omega))
  have htail : ∀ env,J steps.length env → normEnvBound C env → EvalAll P env (.call (b+33) linObjectGlueCorePlan.expr)
      (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
        cost ≤ A+2*C+1) := by
    intro env hJ hC
    obtain ⟨he,hsmall⟩ := hJ
    change env = I.prefixValues.take 6 at he
    subst env
    have hr : linObjectGlueCorePlan.value (I.prefixValues.take 6) = some I.normalize.value := rfl
    have hcSmall := linObjectGlueOuterCore_spec I ho hh hn h hjmem hjo hjm hjh hjs hsmall
    have hbound : grow (grow^[5] W) ≤ C :=
      (Function.iterate_succ_apply' grow 5 W).symm.trans_le (hle 6 8 (by decide))
    have hc1 : FunAll P (b+33) I.normalize.value (fun out cost =>
        AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧ cost ≤ C) :=
      hcSmall.mono fun out cost hout => ⟨hout.1,hout.2.trans
        hbound⟩
    have da := linObjectGlueOuterPlan_det (P:=P) hC linObjectGlueCorePlan (by simp [linObjectGlueOuterPlans]) hr
    exact (normBound_call da hc1).mono fun out cost hout => ⟨hout.1,hout.2.2⟩
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
    exact hle 0 8 (by decide)
  have heval := linObjectCallSteps_spec steps (.call (b+33) linObjectGlueCorePlan.expr) J
    (AnsC (Equiv.refl (Fin n)) · (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y))) harg hstep htail [I.value] hinit hw
  apply FunAll.intro h.entry
  refine heval.mono fun out cost hout => ⟨hout.1,?_⟩
  have hcst : cost ≤ (A+2*C+(A+2*C+1)+5)*243 := hout.2
  exact linObjectGlue_collect hcst

theorem linObjectGlue_uniform (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hv : VectorStabilizer) :
    ∃ K D : ℕ,∀ W,linObjectGlueCost hs hm ho hc hh hn hv W ≤ K*(W+1)^D := by
  obtain ⟨K,D,hKD⟩ := linPoly_source_bound (linObjectGlueCost_poly hs hm ho hc hh hn hv)
  exact ⟨K,D,fun W => hKD 0 W W (Nat.zero_le _) le_rfl⟩

end GI.Impl
