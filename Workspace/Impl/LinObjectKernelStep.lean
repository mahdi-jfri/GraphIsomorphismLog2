module

public import Workspace.Impl.LinObjectKernelCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectKernel_step_spec {P : Program} {b jsci n i : ℕ} {hs : SolvableCosetIntersection}
    (h : linObjectKernelAt P b jsci hs) (as : List (Equiv.Perm (Fin n))) (groups : List Val)
    (acc bv : Val) (K B : Subgroup (Equiv.Perm (Fin n)))
    (hi : groups[i]? = some bv) (hacc : GroupValC n acc K) (hB : GroupValC n bv B)
    (hsol : GI.Lang.Normalizes B K) :
    let input := Val.list [encGroup as,.list groups]
    EvalAll P [.list [input,.nat i,acc]] (linObjectKernelStepF jsci (b + 3))
      (fun out cost => GroupValC n out (K ⊓ B) ∧ cost ≤ linObjectKernelStepCost hs n input.wt) := by
  let input := Val.list [encGroup as,.list groups]
  let W := input.wt
  let M := linObjectKernelAccWt n
  let T := linObjectKernelReadWt n W
  let PB := linObjectKernelPrimBudget hs n
  let G := 8 * mkGroupK * (n + 1) ^ 9
  let pack := 100000 * (T + 3) ^ 2
  let root := Val.list [input,.nat i,acc]
  obtain ⟨hT,wT,mT⟩ := linObjectKernel_read_bounds n W
  have wa : acc.wt ≤ M := linObjectKernel_acc_wt hacc
  have wb : bv.wt ≤ M := linObjectKernel_acc_wt hB
  have hg : (Val.list groups).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hi' : i < groups.length := (List.getElem?_eq_some_iff.mp hi).choose
  have hlen := length_lt_wt_list groups
  have hni := wt_nat_le i
  have wroot : root.wt ≤ T :=
    linObjectKernel_root_wt input acc i W M le_rfl wa (by omega)
  have e0 : normEnvBound T [root] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact wroot
  have rk := linObjectEvalRead (P := P) e0 (slot := 0) rfl [2] rfl (by decide) (by decide) hT
  have rl := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,1] rfl (by decide) (by decide) hT
  have ri := linObjectEvalRead (P := P) e0 (slot := 0) rfl [1] rfl (by decide) (by decide) hT
  have ro := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,0,1,0] rfl (by decide) (by decide) hT
  have db := Det.get' rl.2 ri.2 hi
  have db' := db.mono (linObjectKernel_get_budget T bv.wt (wb.trans mT))
  have dargs := linObjectEvalPack3 (by omega : acc.wt ≤ (T + 1) + 1)
    (by omega : bv.wt ≤ (T + 1) + 1) (by omega : (encPerm (1 : Equiv.Perm (Fin n))).wt ≤ (T + 1) + 1)
    (rk.2.mono (linObjectKernel_read_budget T)) db' (ro.2.mono (linObjectKernel_read_budget T))
  have dargs' : Det P [root]
      (mk3 (arg 2) (.get (.get (arg 0) (.nat 1)) (arg 1))
        (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0)))
      (.list [acc,bv,encPerm (1 : Equiv.Perm (Fin n))]) pack := dargs
  apply EvalAll.letE (solvableCosetIntersection_call hs h.prim dargs' hacc.groupVal hsol hB.groupVal)
  intro out cp hout
  have wprim := CosetIntOut.wt_le hout.1
  have hcp := hout.2
  rcases hout.1 with hfail | ⟨y,hy,hyB,L,he,hL⟩
  · exfalso
    have hn := hfail.2 1 K.one_mem
    exact hn (by simpa using B.one_mem)
  · subst out
    obtain ⟨bs,hbs,hbslen,hmake,hgroup,hwt⟩ := mkGroup_gensVal h.make hL
    have wp : (Val.list [encPerm y,L]).wt ≤ T := by
      have hM : M = 320 * (n + 1) ^ 6 := rfl
      omega
    have e1 : normEnvBound T [root,.list [encPerm y,L]] := normEnvBound_snoc e0 le_rfl wp
    have rn := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0,0,0] rfl (by decide) (by decide) hT
    have rL := linObjectEvalRead (P := P) e1 (slot := 1) rfl [1] rfl (by decide) (by decide) hT
    have dm := linObjectEvalPack2 (by omega : (Val.nat n).wt ≤ (T + 1) + 1)
      (by omega : L.wt ≤ (T + 1) + 1) (rn.2.mono (linObjectKernel_read_budget T))
      (rL.2.mono (linObjectKernel_read_budget T))
    have dm' : Det P [root,.list [encPerm y,L]]
        (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.var 1) (.nat 1))) (.list [.nat n,L]) pack := dm
    have hgen : gens bs = K ⊓ B := GroupVal.unique ⟨bs,rfl,rfl⟩ hgroup
    have dout := Det.call dm' hmake
    refine dout.post fun ct hct => ⟨⟨bs,rfl,hgen,hbslen⟩,?_⟩
    have hpb : (solvableCosetIntersectionPrim hs).bound (.list [acc,bv,encPerm (1 : Equiv.Perm (Fin n))]) ≤ PB :=
      linObjectKernel_prim_bound hs hacc hB
    have hret : (encGroup bs).wt ≤ T := hwt.trans mT
    have hextra : 40 * (n + 1) ^ 6 ≤ T := by
      have hM : M = 320 * (n + 1) ^ 6 := rfl
      omega
    have hbound : cp + ct + (encGroup bs).wt + 1 ≤ 2 * pack + PB + G + 3 * T + 3 := by omega
    exact hbound.trans (linObjectKernel_pack_bound T PB G)

end GI.Impl
