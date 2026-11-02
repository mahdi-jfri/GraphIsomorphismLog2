import Workspace.Impl.LinObjectGlueSuffixSpec

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

set_option maxHeartbeats 500000 in
set_option maxRecDepth 3000 in
theorem linObjectGlueFinish_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm)) (hjh : P.prims[jh]? = some (linHermitePrim hh))
    (env : List Val) (hi : linObjectGluePrefixInv I 6 env)
    (hW : normEnvBound ((linObjectGlueGrow hs hm ho hc hh hn hv)^[6] I.value.wt) env) :
    let C := (linObjectGlueGrow hs hm ho hc hh hn hv)^[10] I.value.wt
    EvalAll P env (.ite linObjectGlueTestPlan.expr
      (linObjectCallStepsE (linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426)) linObjectGlueOutPlan.expr) .nil)
      (fun out cost => AnsC (Equiv.refl (Fin n)) out (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)) ∧
        cost ≤ 100*(linObjectGlueArgBudget C+2*C+100)*3^5) := by
  let grow := linObjectGlueGrow hs hm ho hc hh hn hv
  let C := grow^[10] I.value.wt
  let A := linObjectGlueArgBudget C
  have hle : grow^[6] I.value.wt ≤ C := linObjectInflationary_iter_le grow
    (linObjectGlueGrow_le hs hm ho hc hh hn hv) I.value.wt (by decide)
  have hC : normEnvBound C env := fun v hv' => (hW v hv').trans hle
  obtain ⟨F,xv,u,rfl,hu⟩ := hi
  rcases hu with ⟨rfl,hT⟩ | ⟨r,ls,rfl,hl,hT⟩
  · have hempty : Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hh' := (I.affine_nonempty F).mpr ⟨t,ht⟩
      rw [hT] at hh'
      exact Set.not_nonempty_empty hh'
    have dt := linObjectGluePlan_det (P:=P) hC linObjectGlueTestPlan (by simp [linObjectGluePlans])
      (v:=Val.nat 0) rfl
    have dd := Det.ite_zero dt (Det.nil (P:=P) (env:=I.prefixValues F xv++[.list []]))
      (t:=linObjectCallStepsE (linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426)) linObjectGlueOutPlan.expr)
    refine dd.post fun cost hcost => ⟨Or.inl ⟨rfl,hempty⟩,?_⟩
    change _ ≤ 100*(A+2*C+100)*243
    have hn0 : (Val.list []).wt = 4 := rfl
    change cost ≤ linObjectGlueArgBudget C+5+(Val.list []).wt+1 at hcost
    change cost ≤ A+5+(Val.list []).wt+1 at hcost
    omega
  · change I.affineSet F = (fun l => r*l) '' (gens ls : Set (Equiv.Perm (Fin n))) at hT
    have hsuc := I.affine_success F r ls hT
    have hsf := linObjectGlueSuffix_spec I ho hh hn h hjmem hjh F xv r ls hsuc hW
    have dt := linObjectGluePlan_det (P:=P) hC linObjectGlueTestPlan (by simp [linObjectGluePlans])
      (v:=Val.nat 2) rfl
    apply EvalAll.ite dt (fun v cost ho' => ⟨2,ho'.1⟩)
    intro q ct hq
    have heq : q = 2 := Val.nat.inj hq.1
    subst q
    rw [if_neg (by decide : ¬(2:ℕ) = 0)]
    refine hsf.wt_lt.mono fun out cost hout => ⟨hout.1.1,?_⟩
    have hct : ct ≤ A := hq.2
    have hcst : cost ≤ (A+2*C+A+5)*27 := hout.1.2
    have wo := hout.2
    change _ ≤ 100*(A+2*C+100)*243
    omega

end GI.Impl
