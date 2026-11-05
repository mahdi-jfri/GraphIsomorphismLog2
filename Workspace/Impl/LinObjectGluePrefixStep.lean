module

public import Workspace.Impl.LinObjectGlueSize

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

theorem linObjectGluePrefixInv_root {i : ℕ} {env : List Val} (hi : i ≤ 6) (h : linObjectGluePrefixInv I i env) :
    env[0]? = some I.value := by
  interval_cases i
  · exact h ▸ rfl
  · obtain ⟨F,rfl⟩ := h; rfl
  · obtain ⟨F,xv,rfl⟩ := h; rfl
  · obtain ⟨F,xv,rfl⟩ := h; rfl
  · obtain ⟨F,xv,rfl⟩ := h; rfl
  · obtain ⟨F,xv,rfl⟩ := h; rfl
  · obtain ⟨F,xv,u,rfl,_⟩ := h; rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 3500 in
theorem linObjectGluePrefixStep_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv T : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjo : P.prims[jo]? = some (groupOrderPrim ho)) (hjm : P.prims[jm]? = some (linMembershipPrim hc))
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn))
    (i f : ℕ) (p : linObjectReadPlan)
    (hp : (linObjectGluePrefixSteps (b+1) (b+347) (b+2779) (b+449) (b+2776) (b+683))[i]? = some (f,p))
    (env : List Val) (hI : linObjectGluePrefixInv I i env) (hW : normEnvBound T env) :
    ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost =>
      linObjectGluePrefixInv I (i+1) (env++[out]) ∧ cost ≤ linObjectGlueGrow hs hm ho hc hh hn hv T) := by
  have hil : i < 6 := by
    obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
    simpa only [linObjectGluePrefixSteps,List.length_cons,List.length_nil] using hi
  have hpMem : p ∈ linObjectGluePlans := by
    have hm' := List.mem_of_getElem? hp
    simp only [linObjectGluePrefixSteps,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at hm'
    rcases hm' with h | h | h | h | h | h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [linObjectGluePlans]
  have hwRoot : I.value.wt ≤ T := normEnvBound_get hW (linObjectGluePrefixInv_root I (by omega) hI)
  have hnT : n ≤ T := I.size_bounds.1.trans hwRoot
  have hMT : I.Y.length+I.X.length ≤ T := I.size_bounds.2.trans hwRoot
  have hb {input : Val} {M : ℕ} (hr : p.value env = some input) (hM : M ≤ T) :
      linObjectGlueAllCost hs hm ho hc hh hn hv n input.wt M ≤ linObjectGlueGrow hs hm ho hc hh hn hv T :=
    linObjectGlueGrow_bound hs hm ho hc hh hn hv hnT (linObjectGluePlan_det (P:=P) hW p hpMem hr).wt_lt.le hM
  interval_cases i
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = [I.value] at hI
    subst env
    let input := Val.list [encGroup I.as,encGroup I.ns,tmGlObjsVal I.X,tmGlObjsVal I.Y]
    have hr : linObjectGlueDataPlan.value [I.value] = some input := rfl
    have hms : I.Y.length ≤ input.wt := by
      have hy := length_lt_wt_list (I.Y.map tmGlObjVal)
      have hw : (tmGlObjsVal I.Y).wt < input.wt := wt_le_wt_list (by simp [input])
      simp only [List.length_map] at hy
      change I.Y.length < (tmGlObjsVal I.Y).wt at hy
      omega
    have hcst := hb hr (show I.Y.length ≤ T by omega)
    refine ⟨input,hr,?_⟩
    refine (linObjectData_spec ho hh hn h.data hjo hjm hjh hjs I.as I.ns (linObjectCanonicalProjection I.as I.ns)
      I.X I.Y I.norm_Y I.NA (I.normalN.mono I.AH) I.abelian I.compact le_rfl I.fixY I.targetOK hms).mono
      fun out cost hout => ⟨?_,?_⟩
    · obtain ⟨F,hF⟩ := linObjectGlueFrame_exists I.Y hout.1
      exact ⟨F,by rw [← hF]; rfl⟩
    · have hown : cost ≤ linObjectDataCost hs hm ho hc hh hn input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨F,rfl⟩ := hI
    let input := Val.list [encGroup I.as,encGroup I.ns,tmGlObjsVal I.X]
    have hr : linObjectGluePiecesPlan.value [I.value,F.value] = some input := rfl
    have hcst := hb hr hMT
    have hokX : TmRecObjOK (I.Y.length+I.X.length) I.X := fun o ho =>
      ⟨(I.jointOK o (List.mem_append_right _ ho)).1,(I.jointOK o (List.mem_append_right _ ho)).2.1,
        fun o' ho' he => (I.jointOK o (List.mem_append_right _ ho)).2.2 o' (List.mem_append_right _ ho') he⟩
    refine ⟨input,hr,?_⟩
    refine (linObjectPieces_spec h.pieces I.as I.ns I.X I.norm_X I.NA (I.normalN.mono I.AH)
      I.abelian I.compact (show I.X.length ≤ I.Y.length+I.X.length by omega) I.fixX hokX).mono
      fun out cost hout => ⟨?_,?_⟩
    · obtain ⟨ws,rfl,_⟩ := hout.1
      exact ⟨F,.list ws,rfl⟩
    · have hown : cost ≤ linObjectPiecesCost hs hm n (I.Y.length+I.X.length) input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨F,xv,rfl⟩ := hI
    let input := Val.list [encGroup I.bs,encPerm I.τ]
    have hr : linObjectGlueConjugatePlan.value ((I.prefixValues F xv).take 3) = some input := rfl
    have hcst := hb hr (show 0 ≤ T from Nat.zero_le _)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (linAffineLeft_spec h.conjugate I.bs I.τ) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]
      exact ⟨F,xv,rfl⟩
    · have hown : cost ≤ linAffineLeftCost input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨F,xv,rfl⟩ := hI
    let ctx := Val.list [encGroup I.as,encGroup I.ns,.list ((tmRiPcsO (gens I.as) I.Y).map tmGlObjsVal),
      encIntMatrix F.V,linVecVal (fun i => F.D i i)]
    let input := Val.list [ctx,.list ((tmRiPcsO (gens I.as) I.X).map tmGlObjsVal),encPerm I.τ]
    have hr : linObjectGlueCoordinatePlan.value ((I.prefixValues F xv).take 4) = some input := rfl
    have hcst := hb hr (show 0 ≤ T from Nat.zero_le _)
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (linObjectGlueFrame_coordinate_spec h.coordinate I.as I.ns I.Y I.X F I.jointOK
      I.norm_YX I.NA (gens I.hs) I.AH I.normalA I.normalN I.abelian I.compact I.fixY I.fixX
      I.τ I.τH I.source_conf) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]
      exact ⟨F,xv,rfl⟩
    · have hown : cost ≤ linObjectSourceCoordinateCost hs hm hc input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨F,xv,rfl⟩ := hI
    let d := I.as.length*(tmRiPcsO (gens I.as) I.Y).length
    let input := Val.list [.nat d,encInt 0]
    have hr : linObjectGlueZeroPlan.value ((I.prefixValues F xv).take 5) = some input := by
      simp [linObjectGlueZeroPlan,linObjectReadPlan.value,linObjectReadPlan.list,linObjectGlueProblem.prefixValues,
        linObjectGlueFrame.value,normReadVal,linVecVal,input,d,encInt,linBitsVal]
    have wd : d ≤ T := (linObjectGlueFrame.dimension_le I F).trans (normEnvBound_get hW (slot:=1) rfl)
    have hcst := hb hr wd
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (linObjectZeroRow_spec h.zero d) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]
      exact ⟨F,xv,rfl⟩
    · unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGluePrefixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨F,xv,rfl⟩ := hI
    let ctx := Val.list [encGroup I.as,encGroup I.ns,.list ((tmRiPcsO (gens I.as) I.Y).map tmGlObjsVal),
      encIntMatrix F.V,linVecVal (fun i => F.D i i)]
    let input := Val.list [ctx,encGroup I.coverGenerators,
      linVecVal (0 : Fin (I.as.length*(tmRiPcsO (gens I.as) I.Y).length) → ℤ),
      linFiniteIntVecVal (tmGLQMod F.D) (F.point (tmGlMs I.X ↼ I.τ))]
    have hr : linObjectGlueAffinePlan.value ((I.prefixValues F xv).take 6) = some input := rfl
    have hcst := hb hr (show 0 ≤ T from Nat.zero_le _)
    refine ⟨input,hr,?_⟩
    have hh' := linObjectGlueFrame_affine_spec hh h.affine hjh I.as I.ns I.Y F I.targetOK I.norm_Y I.NA
      I.coverGenerators I.A_cover (I.normalA.mono I.cover_H) (I.normalN.mono I.cover_H) I.abelian I.compact
      I.fixY I.cover_conf (I.solvable_rep F) 0 (F.point (tmGlMs I.X ↼ I.τ))
    rw [linFiniteIntVecVal_zero] at hh'
    refine hh'.mono fun out cost hout => ⟨?_,?_⟩
    · exact ⟨F,xv,out,rfl,hout.1⟩
    · have hown : cost ≤ linObjectCallerCost hs hm hc hh hv input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega

end GI.Impl
