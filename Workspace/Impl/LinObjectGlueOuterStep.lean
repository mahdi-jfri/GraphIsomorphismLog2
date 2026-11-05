module

public import Workspace.Impl.LinObjectGlueOuterPrefix

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

variable {n : ℕ} (I : linObjectGlueRaw n)

set_option maxHeartbeats 500000 in
set_option maxRecDepth 2500 in
theorem linObjectGlueOuterStep_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv T : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm))
    (i f : ℕ) (p : linObjectReadPlan)
    (hp : (linObjectGlueOuterSteps (b+1) (b+4) (b+25) (b+28))[i]? = some (f,p))
    (env : List Val) (hI : linObjectGlueOuterInv I i env) (hW : normEnvBound T env) :
    ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost =>
      linObjectGlueOuterInv I (i+1) (env++[out]) ∧ cost ≤ linObjectGlueOuterGrow hs hm ho hc hh hn hv T) := by
  have hil : i < 5 := by
    obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
    simpa only [linObjectGlueOuterSteps,List.length_cons,List.length_nil] using hi
  have hpMem : p ∈ linObjectGlueOuterPlans := by
    have hm' := List.mem_of_getElem? hp
    simp only [linObjectGlueOuterSteps,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at hm'
    rcases hm' with h | h | h | h | h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [linObjectGlueOuterPlans]
  have hwRoot : I.value.wt ≤ T := normEnvBound_get hW (linObjectGlueOuterInv_root I hI)
  have hnT : n ≤ T := I.size_bounds.1.trans hwRoot
  have hMT : I.as.length ≤ T := I.size_bounds.2.trans hwRoot
  have hb {input : Val} {M : ℕ} (hr : p.value env = some input) (hM : M ≤ T) :
      linObjectGlueOuterAllCost hs hm ho hc hh hn hv n input.wt M ≤ linObjectGlueOuterGrow hs hm ho hc hh hn hv T :=
    linObjectGlueOuterGrow_bound hs hm ho hc hh hn hv hnT
      (linObjectGlueOuterPlan_det (P:=P) hW p hpMem hr).wt_lt.le hM
  interval_cases i
  · simp only [linObjectGlueOuterSteps,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = I.prefixValues.take 1 at hI
    subst env
    let input := Val.list [tmGlObjsVal I.Y,tmGlObjsVal I.X]
    have hr : linObjectGlueJoinPlan.value (I.prefixValues.take 1) = some input := rfl
    have hcst := hb hr (Nat.zero_le T)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (linAppend_spec h.append (I.Y.map tmGlObjVal) (I.X.map tmGlObjVal)) fun out cost hout => ⟨?_,?_⟩
    · have he : out = tmGlObjsVal (I.Y++I.X) := by simpa only [tmGlObjsVal,List.map_append] using hout.1
      exact he ▸ rfl
    · have hown : cost ≤ linAppendCost input.wt := hout.2
      unfold linObjectGlueOuterAllCost at hcst
      omega
  · simp only [linObjectGlueOuterSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = I.prefixValues.take 2 at hI
    subst env
    let input := tmGlObjsVal (I.Y++I.X)
    have hr : linObjectGlueNormalizePlan.value (I.prefixValues.take 2) = some input := rfl
    have hcst := hb hr (Nat.zero_le T)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (linObjectNormalize_spec hm h.normalize hjmem (I.Y++I.X)) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]; rfl
    · have hown : cost ≤ linObjectNormalizeCost hm input.wt := hout.2
      unfold linObjectGlueOuterAllCost at hcst
      omega
  · simp only [linObjectGlueOuterSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = I.prefixValues.take 3 at hI
    subst env
    let input := Val.list [.nat 0,.nat I.Y.length,tmGlObjsVal I.normalizedAll]
    have hr : linObjectGlueTargetPlan.value (I.prefixValues.take 3) = some input := by
      simp [linObjectGlueTargetPlan,linObjectReadPlan.value,linObjectReadPlan.list,linObjectGlueRaw.prefixValues,
        linObjectGlueRaw.value,tmGlIn,tmGlObjsVal,normReadVal,input]
    have hcst := hb hr (Nat.zero_le T)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (I.target_slice_spec h.slice) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]; rfl
    · have hown : cost ≤ linSliceCost input.wt := hout.2
      unfold linObjectGlueOuterAllCost at hcst
      omega
  · simp only [linObjectGlueOuterSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = I.prefixValues.take 4 at hI
    subst env
    let input := Val.list [.nat I.Y.length,.nat I.X.length,tmGlObjsVal I.normalizedAll]
    have hr : linObjectGlueSourcePlan.value (I.prefixValues.take 4) = some input := by
      simp [linObjectGlueSourcePlan,linObjectReadPlan.value,linObjectReadPlan.list,linObjectGlueRaw.prefixValues,
        linObjectGlueRaw.value,tmGlIn,tmGlObjsVal,normReadVal,input]
    have hcst := hb hr (Nat.zero_le T)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (I.source_slice_spec h.slice) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]; rfl
    · have hown : cost ≤ linSliceCost input.wt := hout.2
      unfold linObjectGlueOuterAllCost at hcst
      omega
  · simp only [linObjectGlueOuterSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = I.prefixValues.take 5 at hI
    subst env
    let input := encGroup I.as
    have hr : linObjectGlueReducePlan.value (I.prefixValues.take 5) = some input := rfl
    have hcst := hb hr hMT
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (reduce_spec hm h.reduce hjmem I.as) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]; rfl
    · unfold linObjectGlueOuterAllCost at hcst
      omega

end GI.Impl
