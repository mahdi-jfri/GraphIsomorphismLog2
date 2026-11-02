import Workspace.Impl.LinObjectGlueSuffix

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset GI.Assembly
open scoped IsMulCommutative

theorem linObjectToFin_refl {n : ℕ} (A : Set (Equiv.Perm (Fin n))) : toFin (Equiv.refl (Fin n)) '' A = A := by
  have hh : ∀ a : Equiv.Perm (Fin n),toFin (Equiv.refl (Fin n)) a = a := fun a => by
    ext; simp [Equiv.permCongr_apply]
  simp [hh]

theorem linObjectAnsC_left {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (X Y : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (t : Equiv.Perm (Fin n))
    (ht : t ∈ Iso H X Y) (gv : Val) (hg : GroupValC n gv (Aut H Y)) :
    AnsC (Equiv.refl (Fin n)) (.list [encPerm t,gv]) (Iso H X Y) := by
  obtain ⟨gs,rfl,hgs,hl⟩ := hg
  refine Or.inr ⟨t,gs,rfl,hl,?_⟩
  rw [linObjectToFin_refl]
  change Iso H X Y = (fun g => t*g) '' (gens gs : Set (Equiv.Perm (Fin n)))
  rw [hgs]
  exact linObjectIso_leftCoset H X Y t ht

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

set_option maxHeartbeats 700000 in
set_option maxRecDepth 3000 in
theorem linObjectGlueSuffix_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm)) (hjh : P.prims[jh]? = some (linHermitePrim hh))
    (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val) (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n)))
    (hsuccess : linObjectGlueSuccessData I F r ls)
    (hW : normEnvBound ((linObjectGlueGrow hs hm ho hc hh hn hv)^[6] I.value.wt)
      (linObjectGlueSuffixBase I F xv r ls)) :
    let C := (linObjectGlueGrow hs hm ho hc hh hn hv)^[10] I.value.wt
    EvalAll P (linObjectGlueSuffixBase I F xv r ls)
      (linObjectCallStepsE (linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426)) linObjectGlueOutPlan.expr)
      (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
        cost ≤ (linObjectGlueArgBudget C+2*C+linObjectGlueArgBudget C+5)*3^3) := by
  let grow := linObjectGlueGrow hs hm ho hc hh hn hv
  let W := I.value.wt
  let C := grow^[10] W
  let steps := linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426)
  let J := fun i env => linObjectGlueSuffixInv I F xv r ls i env ∧ normEnvBound (grow^[6+i] W) env
  have hle (i j : ℕ) (hi : i ≤ j) : grow^[i] W ≤ grow^[j] W :=
    linObjectInflationary_iter_le grow (linObjectGlueGrow_le hs hm ho hc hh hn hv) W hi
  have harg : ∀ fp ∈ steps,linObjectPlanBudget fp.2 C ≤ linObjectGlueArgBudget C := by
    intro fp hp
    have hm' : fp.2 ∈ linObjectGluePlans := by
      simp only [steps,linObjectGlueSuffixSteps,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [linObjectGluePlans]
    exact linObjectGluePlanBudget_le _ _ hm'
  have hstep : ∀ i f p,steps[i]? = some (f,p) → ∀ env,J i env → normEnvBound C env →
      ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost => J (i+1) (env++[out]) ∧ cost ≤ C) := by
    intro i f p hp env hJ hC
    have hil : i < 3 := by
      obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
      simpa only [steps,linObjectGlueSuffixSteps,List.length_cons,List.length_nil] using hi
    obtain ⟨input,hr,hcall⟩ := linObjectGlueSuffixStep_spec I ho hh hn h hjmem hjh F xv r ls hsuccess i f p hp env hJ.1 hJ.2
    refine ⟨input,hr,hcall.wt_lt.mono fun out cost hout => ⟨⟨hout.1.1,?_⟩,?_⟩⟩
    · have hw' : normEnvBound (grow (grow^[6+i] W)) (env++[out]) :=
        normEnvBound_snoc hJ.2 (linObjectGlueGrow_le hs hm ho hc hh hn hv _) (hout.2.le.trans hout.1.2)
      change normEnvBound (grow^[6+i+1] W) (env++[out])
      rw [Function.iterate_succ_apply']
      exact hw'
    · have hcost : cost ≤ grow^[6+i+1] W := by
        simpa only [Function.iterate_succ_apply'] using hout.1.2
      exact hcost.trans (hle _ 10 (by omega))
  have htail : ∀ env,J steps.length env → normEnvBound C env → EvalAll P env linObjectGlueOutPlan.expr
      (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
        cost ≤ linObjectGlueArgBudget C) := by
    intro env hJ hC
    obtain ⟨t,ht,gv,rfl,hgv⟩ := hJ.1
    have dd := linObjectGluePlan_det (P:=P) hC linObjectGlueOutPlan (by simp [linObjectGluePlans])
      (v:=Val.list [encPerm t,gv]) rfl
    exact dd.post fun cost hcost => ⟨linObjectAnsC_left _ _ _ t ht gv hgv,hcost⟩
  exact linObjectCallSteps_spec steps linObjectGlueOutPlan.expr J
    (AnsC (Equiv.refl (Fin n)) · (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y))) harg hstep htail
    (linObjectGlueSuffixBase I F xv r ls) ⟨rfl,hW⟩
    (fun v hv' => (hW v hv').trans (hle 6 10 (by decide)))

end GI.Impl
