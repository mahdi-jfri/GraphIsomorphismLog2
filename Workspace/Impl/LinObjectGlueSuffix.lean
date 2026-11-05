module

public import Workspace.Impl.LinObjectGlueSuccess
public import Workspace.Impl.LinObjectGlueSize

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

noncomputable def linObjectGlueSuffixBase (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val)
    (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n))) : List Val :=
  I.prefixValues F xv++[.list [encPerm r,encGroup ls]]

def linObjectGlueSuffixInv (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val)
    (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n))) (i : ℕ) (env : List Val) : Prop :=
  let base := linObjectGlueSuffixBase I F xv r ls
  match i with
  | 0 => env = base
  | 1 => env = base++[encPerm (I.τ*r)]
  | 2 => ∃ t ∈ Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y),env = base++[encPerm (I.τ*r),encPerm t]
  | 3 => ∃ t ∈ Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y),∃ gv,
      env = base++[encPerm (I.τ*r),encPerm t,gv] ∧ GroupValC n gv (Aut (gens I.hs) (tmGlMs I.Y))
  | _ => False

theorem linObjectGlueSuffixInv_root (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val)
    (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n)))
    {i : ℕ} {env : List Val} (hi : i ≤ 3) (h : linObjectGlueSuffixInv I F xv r ls i env) :
    env[0]? = some I.value := by
  interval_cases i
  · exact h ▸ rfl
  · exact h ▸ rfl
  · obtain ⟨t,ht,rfl⟩ := h; rfl
  · obtain ⟨t,ht,gv,rfl,_⟩ := h; rfl

set_option maxHeartbeats 700000 in
set_option maxRecDepth 3000 in
theorem linObjectGlueSuffixStep_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js jv T : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership}
    {hc : ConstructiveMembership} {hv : VectorStabilizer}
    (h : linObjectGlueCoreAt P b jsci jder jmem jo jm jh js jv hs hd hm hc hv)
    (hjmem : P.prims[jmem]? = some (membershipPrim hm)) (hjh : P.prims[jh]? = some (linHermitePrim hh))
    (F : linObjectGlueFrame I.as I.ns I.Y) (xv : Val) (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n)))
    (hsuccess : linObjectGlueSuccessData I F r ls)
    (i f : ℕ) (p : linObjectReadPlan)
    (hp : (linObjectGlueSuffixSteps (b+2772) (b+2111) (b+2426))[i]? = some (f,p))
    (env : List Val) (hI : linObjectGlueSuffixInv I F xv r ls i env) (hW : normEnvBound T env) :
    ∃ input,p.value env = some input ∧ FunAll P f input (fun out cost =>
      linObjectGlueSuffixInv I F xv r ls (i+1) (env++[out]) ∧ cost ≤ linObjectGlueGrow hs hm ho hc hh hn hv T) := by
  have hil : i < 3 := by
    obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hp
    simpa only [linObjectGlueSuffixSteps,List.length_cons,List.length_nil] using hi
  have hpMem : p ∈ linObjectGluePlans := by
    have hm' := List.mem_of_getElem? hp
    simp only [linObjectGlueSuffixSteps,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at hm'
    rcases hm' with h | h | h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [linObjectGluePlans]
  have hwRoot : I.value.wt ≤ T := normEnvBound_get hW (linObjectGlueSuffixInv_root I F xv r ls (by omega) hI)
  have hnT : n ≤ T := I.size_bounds.1.trans hwRoot
  have hb {input : Val} (hr : p.value env = some input) :
      linObjectGlueAllCost hs hm ho hc hh hn hv n input.wt 0 ≤ linObjectGlueGrow hs hm ho hc hh hn hv T :=
    linObjectGlueGrow_bound hs hm ho hc hh hn hv hnT
      (linObjectGluePlan_det (P:=P) hW p hpMem hr).wt_lt.le (Nat.zero_le _)
  let π := linObjectCanonicalProjection I.as I.ns
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk := linObjectCanonical_ker_local I.as I.ns I.Y I.fixY
  interval_cases i
  · simp only [linObjectGlueSuffixSteps,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = linObjectGlueSuffixBase I F xv r ls at hI
    subst env
    let input := Val.list [encPerm I.τ,encPerm r]
    have hr : linObjectGlueComposePlan.value (linObjectGlueSuffixBase I F xv r ls) = some input := rfl
    have hcst := hb hr
    refine ⟨input,hr,?_⟩
    refine FunAll.mono (compose_spec h.compose I.τ r) fun out cost hout => ⟨?_,?_⟩
    · rw [hout.1]; rfl
    · unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGlueSuffixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    change env = linObjectGlueSuffixBase I F xv r ls++[encPerm (I.τ*r)] at hI
    subst env
    let input := Val.list [encGroup I.as,encGroup I.ns,.list ((tmRiPcsO (gens I.as) I.Y).map tmGlObjsVal),
      linObjectBlockInput F.blocks,.list ((tmRiPcsO (gens I.as) I.X).map tmGlObjsVal),encPerm (I.τ*r)]
    have hr : linObjectGlueCorrectPlan.value (linObjectGlueSuffixBase I F xv r ls++[encPerm (I.τ*r)]) = some input := rfl
    have hcst := hb hr
    refine ⟨input,hr,?_⟩
    have hτr : I.τ*r ∈ gens I.hs := (gens I.hs).mul_mem I.τH (I.cover_H hsuccess.1)
    refine (linObjectSourceCorrect_spec hh h.correct hjh I.as I.ns π hπ F.presentation.2.1 I.Y I.X I.jointOK
      I.norm_YX I.NA (gens I.hs) I.AH I.normalA I.normalN I.abelian I.compact I.fixY I.fixX hk
      F.blocks (by omega) F.fullRank F.localKernel (I.τ*r) hτr (I.source_cover_conf r hsuccess.1)).mono
      fun out cost hout => ⟨?_,?_⟩
    · obtain ⟨a,ha,he,hact⟩ := linObjectCorrectOneAnswer_success (gens I.as) (tmGlMs I.Y)
        (tmGlMs I.X ↼ (I.τ*r)) (I.τ*r) out hout.1 hsuccess.2.1
      refine ⟨I.τ*r*a,⟨(gens I.hs).mul_mem hτr (I.AH ha),by rwa [← act_act]⟩,?_⟩
      rw [he,List.append_assoc]
      rfl
    · have hown : cost ≤ linObjectCorrectOneCost hs hm hc hh input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega
  · simp only [linObjectGlueSuffixSteps,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hp
    obtain ⟨rfl,rfl⟩ := hp
    obtain ⟨t,ht,rfl⟩ := hI
    let ctx := Val.list [encGroup I.as,encGroup I.ns,.list ((tmRiPcsO (gens I.as) I.Y).map tmGlObjsVal),linObjectBlockInput F.blocks]
    let input := Val.list [ctx,.list F.groups,.list ((1::ls).map encPerm)]
    have hr : linObjectGlueStabilizerPlan.value (linObjectGlueSuffixBase I F xv r ls++[encPerm (I.τ*r),encPerm t]) =
        some input := rfl
    have hcst := hb hr
    refine ⟨input,hr,?_⟩
    refine (linObjectStabilizer_spec hh h.stabilizer hjmem hjh I.as I.ns π hπ F.presentation.2.1 I.Y I.targetOK
      I.norm_Y I.NA (gens I.hs) I.AH I.normalA I.normalN I.abelian I.compact I.fixY hk
      F.blocks (by omega) F.fullRank F.localKernel F.groups F.localGroups (1::ls)
      (fun g hg => (hsuccess.2.2.1 g hg).1) (fun g hg => (hsuccess.2.2.1 g hg).2.1)
      (fun g hg => (hsuccess.2.2.1 g hg).2.2) hsuccess.2.2.2).mono fun out cost hout => ⟨?_,?_⟩
    · exact ⟨t,ht,out,rfl,hout.1⟩
    · have hown : cost ≤ linObjectStabilizerCost hs hm hc hh input.wt := hout.2
      unfold linObjectGlueAllCost at hcst
      omega

end GI.Impl
