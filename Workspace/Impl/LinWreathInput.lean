import Workspace.Impl.LinWreathInputCompose

/-! The two-copy task input is computed from the source task's encoding and
its target vector, at a fixed polynomial cost in their input weight. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linWreathInput_spec {P : Program} {b : ℕ} (h : linWreathInputAt P b)
    (I : VecStabInst) [Nonempty (Fin I.n)] (hd : 0 < I.d) (w : Fin I.d → ZMod I.p) :
    FunDet P b (.list [vecStabEnc I, encVec w]) (vecStabEnc (linWreathVecInst I w))
      (linWreathInputCost (Val.list [vecStabEnc I, encVec w]).wt) := by
  let As := linWreathOldMatrices I
  let ms := Val.list (As.map encModMatrix)
  let vs := (List.finRange I.d).map (fun i => Val.nat (I.v i).val)
  let ws := (List.finRange I.d).map (fun i => Val.nat (w i).val)
  let src := Val.list [encGroup I.gs, .nat I.p, ms, .list vs]
  let a := Val.list [src, .list ws]
  let W := a.wt
  let raw := Val.list (encPerm (1 : Perm (Fin I.n)) :: I.gs.map encPerm)
  let tail := Val.list (I.gs.map encPerm)
  let perms := Val.list ((linWreathCoverGenerators I.gs).map encPerm)
  let gv := encGroup (linWreathCoverGenerators I.gs)
  let mats := linWreathMatrices hd As
  let vec := Val.list (vs ++ ws)
  have hsrc : vecStabEnc I = src := by
    unfold vecStabEnc
    rw [linWreathOldMatrices_value]
    rfl
  have hw : encVec w = .list ws := rfl
  rw [hsrc, hw, linWreathVecInst_encoding I w hd]
  have wsrc : src.wt < W := wt_le_wt_list (by simp [W, a])
  have wws : (Val.list ws).wt < W := wt_le_wt_list (by simp [W, a])
  have wH : (encGroup I.gs).wt < src.wt := wt_le_wt_list (by simp [src])
  have wms : ms.wt < src.wt := wt_le_wt_list (by simp [src])
  have wvs : (Val.list vs).wt < src.wt := wt_le_wt_list (by simp [src])
  have wraw : raw.wt < (encGroup I.gs).wt := wt_le_wt_list (by simp [raw, encGroup, encPerms])
  have wid : (encPerm (1 : Perm (Fin I.n))).wt < raw.wt := wt_le_wt_list (by simp [raw])
  have wtail : tail.wt ≤ (encGroup I.gs).wt := wt_gens_le_encGroup I.gs
  have hmeasure := S_le_wt_encGroup I.gs
  have hn : I.n ≤ W := by nlinarith
  have htlen : I.gs.length ≤ W := by nlinarith
  have hdW : I.d ≤ W := by
    have hh := length_lt_wt_list vs
    have he : vs.length = I.d := by simp [vs]
    rw [he] at hh
    omega
  have wperm : (Val.list [encPerm (1 : Perm (Fin I.n)), tail]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encPerm (1 : Perm (Fin I.n))) tail
    omega
  have wmat : (Val.list [ms, .nat I.d]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le ms (.nat I.d)
    have wd := wt_nat_le I.d
    omega
  have htail : FunDet P (b + 1) raw tail (linTailCost W) := by
    have hh := linTail_spec h.tail (encPerm (1 : Perm (Fin I.n)) :: I.gs.map encPerm)
    simp only [List.drop_succ_cons, List.drop_zero] at hh
    refine hh.mono ?_
    unfold linTailCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      change raw.wt + 1 ≤ W + 1
      omega) 3)
  have hperms : FunDet P (b + 4) (.list [encPerm (1 : Perm (Fin I.n)), tail]) perms
      (linWreathInputPermBudget W) :=
    (linWreathPerm_spec h.perms I.gs).mono (linWreathPermCost_mono wperm hn)
  have hgroup : FunDet P (b + 32) (.list [.nat (I.n + I.n), perms]) gv
      (linWreathInputGroupBudget W) := by
    refine (mkGroup_spec h.group (linWreathCoverGenerators I.gs)).mono ?_
    rw [linWreathCoverGenerators_length]
    unfold linWreathInputGroupBudget
    apply Nat.mul_le_mul_left _
    apply Nat.pow_le_pow_left
    exact Nat.mul_le_mul (by omega) (by omega)
  have hmatrices : FunDet P (b + 39) (.list [ms, .nat I.d]) mats
      (linWreathInputMatrixBudget W) :=
    (linWreathMatrices_spec h.matrices I.prime hd As).mono (linWreathMatricesCost_mono wmat hdW)
  have hvector : FunDet P (b + 68) (.list [.list vs, .list ws]) vec
      (linWreathInputVectorBudget W) := by
    refine (linAppend_det h.append vs ws).mono ?_
    have hlen : ws.length = I.d := by simp [ws]
    rw [hlen]
    have warg := wt_list2_le (.list vs) (.list ws)
    have wout := linListAppendWt vs ws
    unfold linWreathInputVectorBudget
    simp only [loopModK]
    have hh : (Val.list [.list vs, .list ws]).wt + I.d + (Val.list (vs ++ ws)).wt + 1 ≤
        100 * (W + 1) := by omega
    calc 1000 * (I.d + 1) * ((Val.list [.list vs, .list ws]).wt + I.d + (Val.list (vs ++ ws)).wt + 1)
        ≤ 1000 * (W + 1) * (100 * (W + 1)) := Nat.mul_le_mul (by omega) hh
      _ = _ := by ring
  have hh := linWreathInputCompose_spec h (encPerm (1 : Perm (Fin I.n))) (.nat I.p) ms perms gv mats vec
    (I.gs.map encPerm) vs ws htail hperms hgroup (by
      simpa only [vs, List.length_map, List.length_finRange] using hmatrices) hvector
  change FunDet P b a (.list [gv, .nat I.p, mats, vec])
    (linWreathInputComposeCost W I.n vs.length (linTailCost W) (linWreathInputPermBudget W)
      (linWreathInputGroupBudget W) (linWreathInputMatrixBudget W) (linWreathInputVectorBudget W)) at hh
  refine hh.mono ?_
  change linWreathInputComposeCost W I.n vs.length (linTailCost W) (linWreathInputPermBudget W)
    (linWreathInputGroupBudget W) (linWreathInputMatrixBudget W) (linWreathInputVectorBudget W) ≤
      linWreathInputCost W
  have hlen : vs.length = I.d := by simp [vs]
  rw [hlen]
  unfold linWreathInputComposeCost linWreathInputCost linWreathInputSum
  omega

end GI.Impl
