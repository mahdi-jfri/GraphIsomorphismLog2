import Workspace.Impl.LinObjectDataWeights
import Workspace.Impl.GenNormGlue

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectDataTailE (locals range product quotient : ℕ) : Expr :=
  .letE (.call range (.arith .add
    (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1)))
    (.letE (.call range (.length (.var 2)))
      (.letE (.call locals (mk2 (mk4 (arg 0) (.var 2) (.var 3) (.var 4)) (.get (.var 1) (.nat 1))))
        (.letE (.call range (.arith .add (.length (.var 2)) (.length (.var 3))))
          (.letE (mk3 (.var 6) (.var 4) (.var 5))
            (.letE (.call product (.var 7))
              (.letE (.call quotient (.var 7))
                (.snoc (mk4 (.var 1) (.var 2) (.var 7) (.var 8)) (.var 9))))))))

noncomputable def linObjectDataTailCost (hs : SolvableCosetIntersection) (hm : Membership)
    (ho : GroupOrder) (hc : ConstructiveMembership) (hh : HermiteFullRank) (hn : SmithNonsingular) (W : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + W + linObjectDataPiecesBudget hs hm W + linObjectDataAbelianBudget ho hc W +
    linObjectDataRangeBudget W + linObjectDataLocalBudget hs hm ho hc W +
    linObjectDataProductBudget hs hm ho hc hh hn W + linObjectDataQuotientBudget hs hm ho hc hh hn W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000 in
theorem linObjectData_tail_spec (ho : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    {P : Program} {b jsci jder jmem jo jm jh js n : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectDataAt P b jsci jder jmem jo jm jh js hs hd hm hc)
    (hjh : P.prims[jh]? = some (linHermitePrim hh)) (hjs : P.prims[js]? = some (linSmithPrim hn))
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (X Y : List (TmRiO n)) (M : Matrix (Fin as.length) (Fin as.length) ℤ)
    (hM : linPermPresentation ns as M) (groups : List Val)
    (hgroups : List.Forall₂ (fun S v => GroupValC n v (Aut (gens as) (tmGlMs S))) (tmRiPcsO (gens as) Y) groups)
    (wp : (Val.list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal), .list groups]).wt ≤
      linObjectDataPiecesBudget hs hm (Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]).wt)
    (wm : (encIntMatrix M).wt ≤ linObjectDataAbelianBudget ho hc
      (Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]).wt) :
    let input := Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]
    let pv := Val.list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal), .list groups]
    EvalAll P [input, pv, encIntMatrix M]
      (linObjectDataTailE (b + 199) (b + 263) (b + 266) (b + 294)) (fun out cost =>
        linObjectDataOut as ns Y π out ∧ cost ≤ linObjectDataTailCost hs hm ho hc hh hn input.wt) := by
  let input := Val.list [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y]
  let W := input.wt
  let refs := tmRiPcsO (gens as) Y
  let N := n ^ 2 + 1
  let PB := linObjectDataPiecesBudget hs hm W
  let AB := linObjectDataAbelianBudget ho hc W
  let RB := linObjectDataRangeBudget W
  let LB := linObjectDataLocalBudget hs hm ho hc W
  let WB := linObjectDataProductBudget hs hm ho hc hh hn W
  let VB := linObjectDataQuotientBudget hs hm ho hc hh hn W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [input, W])
  have hn0 : (Val.nat n).wt ≤ W := by
    have hv : (Val.nat n).wt < (encGroup as).wt := wt_le_wt_list (by simp [encGroup, encPerms])
    exact hv.le.trans wa.le
  have hwA := S_le_wt_encGroup as
  have hdegree : n ≤ W := by
    have hmul : n + 1 ≤ (as.length + 2) * (n + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht : as.length ≤ W := by
    have hmul : as.length + 2 ≤ (as.length + 2) * (n + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
    omega
  have hWsq : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hnPow : n ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (hdegree.trans (Nat.le_succ W)) 2
  have hN : N ≤ 100 * (W + 1) ^ 2 := by dsimp only [N]; omega
  have htR : as.length ≤ 100 * (W + 1) ^ 2 := by omega
  have htotalR : as.length + N ≤ 100 * (W + 1) ^ 2 := by dsimp only [N]; omega
  have hgroup' : List.Forall₂ (fun S v => ∃ bs : List (Equiv.Perm (Fin n)), v = encGroup bs ∧
      (gens bs = Aut (gens as) (tmGlMs S) ∧ bs.length ≤ n ^ 2)) refs groups :=
    hgroups.imp fun _ _ ⟨bs, he, hgen, hlen⟩ => ⟨bs, he, hgen, hlen⟩
  obtain ⟨bss, rfl, hB⟩ := linForall₂_encoded encGroup _ hgroup'
  let pv := Val.list [.list (refs.map tmGlObjsVal), .list (bss.map encGroup)]
  have wg : (Val.list (bss.map encGroup)).wt ≤ PB := by
    have hsub : (Val.list (bss.map encGroup)).wt < pv.wt := wt_le_wt_list (by simp [pv])
    dsimp only [pv, PB, refs, input, W] at *
    omega
  have rangeN : FunDet P (b + 263) (.nat N) (encFun (fun i : Fin N => i.val)) RB :=
    (linRange_spec h.range N).mono
      (linPolyEnvelope_bound linObjectOffsetsRangePoly hN (Nat.zero_le _) (Nat.zero_le _))
  have rangeT : FunDet P (b + 263) (.nat as.length) (encFun (fun i : Fin as.length => i.val)) RB :=
    (linRange_spec h.range as.length).mono
      (linPolyEnvelope_bound linObjectOffsetsRangePoly htR (Nat.zero_le _) (Nat.zero_le _))
  have rangeR : FunDet P (b + 263) (.nat (as.length + N))
      (encFun (fun i : Fin (as.length + N) => i.val)) RB :=
    (linRange_spec h.range (as.length + N)).mono
      (linPolyEnvelope_bound linObjectOffsetsRangePoly htotalR (Nat.zero_le _) (Nat.zero_le _))
  have widN := rangeN.wt_lt.le
  have widT := rangeT.wt_lt.le
  have widR := rangeR.wt_lt.le
  let idsN := encFun (fun i : Fin N => i.val)
  let idsT := encFun (fun i : Fin as.length => i.val)
  let idsR := encFun (fun i : Fin (as.length + N) => i.val)
  have dA := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y])
    (rest := [pv, encIntMatrix M]) (j := 0) rfl
  have dn := Det.get' dA (Det.nat 0) rfl
  have dN := Det.arith' (op := .add) (Det.arith' (op := .mul) dn dn (z := n * n) rfl) (Det.nat 1)
    (z := N) (by simp [N, pow_two])
  apply EvalAll.letE (Det.call dN rangeN)
  intro v cn hv
  obtain ⟨rfl, hcn⟩ := hv
  have dt := Det.length (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN]) (i := 2) rfl)
  simp only [List.length_map, List.length_finRange] at dt
  apply EvalAll.letE (Det.call dt rangeT)
  intro v ct hv
  obtain ⟨rfl, hct⟩ := hv
  let ctx := Val.list [encGroup as, encIntMatrix M, idsN, idsT]
  have hlocalArg : (Val.list [ctx, .list (bss.map encGroup)]).wt ≤ linObjectDataLocalArg hs hm ho hc W := by
    change (Val.list [.list [encGroup as, encIntMatrix M, idsN, idsT], .list (bss.map encGroup)]).wt ≤
      100 * (W + PB + AB + 2 * RB + 1) ^ 2
    exact linObjectDataLocalArg_wt _ _ _ _ _ W PB AB RB wa.le wm widN widT wg
  have hlocal : FunAll P (b + 199) (.list [ctx, .list (bss.map encGroup)])
      (fun out cost => (∃ L : Fin refs.length → Matrix (Fin (as.length + N)) (Fin as.length) ℤ,
        out = .list ((List.finRange refs.length).map fun i => encIntMatrix (L i)) ∧
        (∀ i, ∃ C : Matrix (Fin N) (Fin as.length) ℤ, L i = linRowStack M C ∧
          (linRelations C).map (linObjectLiftCoord as π) =
            linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs (refs.get i)))) ∧
        (∀ i, Function.Injective (L i).mulVec)) ∧ cost ≤ LB) :=
    (linObjectData_local_collection hc h.locals as ns π refs bss M hM hB).mono
      fun out cost ho' => ⟨ho'.1, ho'.2.trans (linPolyEnvelope_bound (linObjectLocalRelationsCost_poly hc)
        (Nat.zero_le _) hlocalArg (Nat.zero_le _))⟩
  have dlA := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X, tmGlObjsVal Y])
    (rest := [pv, encIntMatrix M, idsN, idsT]) (j := 0) rfl
  have dlctx := Det.mk4 dlA
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT]) (i := 2) rfl)
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT]) (i := 3) rfl)
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT]) (i := 4) rfl)
  have dlg := Det.get' (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT]) (i := 1) rfl)
    (Det.nat 1) rfl
  apply EvalAll.letE (normBound_call (Det.mk2 dlctx dlg) hlocal)
  intro lv cl hlv
  obtain ⟨⟨L, rfl, hLC, hfull⟩, wl, hcl⟩ := hlv
  let lv := Val.list ((List.finRange refs.length).map fun i => encIntMatrix (L i))
  have drow := Det.arith' (op := .add)
    (Det.length (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv]) (i := 2) rfl))
    (Det.length (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv]) (i := 3) rfl))
    (z := as.length + N) (by simp [encFun])
  apply EvalAll.letE (Det.call drow rangeR)
  intro v cr hv
  obtain ⟨rfl, hcr⟩ := hv
  have dwin := Det.mk3
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR]) (i := 6) rfl)
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR]) (i := 4) rfl)
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR]) (i := 5) rfl)
  apply EvalAll.letE dwin
  intro v ci hv
  obtain ⟨rfl, hci⟩ := hv
  let win := linObjectBlockInput L
  have hnormArg : win.wt ≤ linObjectDataNormalArg hs hm ho hc W := by
    change (Val.list [idsR, idsT, lv]).wt ≤ 100 * (W + LB + 2 * RB + 1) ^ 2
    exact linObjectDataNormalArg_wt _ _ _ W RB LB widR widT wl
  have hproduct : FunAll P (b + 266) win (fun out cost => TmGLQOut (linObjectBlockMatrix L) out ∧ cost ≤ WB) :=
    (linObjectProductNormal_spec hh hn h.product hjh hjs L (by omega) hfull).mono
      fun out cost ho' => ⟨ho'.1, ho'.2.trans (linPolyEnvelope_bound (linObjectProductNormalAllCost_poly hh hn)
        (Nat.zero_le _) hnormArg (Nat.zero_le _))⟩
  have hquotient : FunAll P (b + 294) win (fun out cost => TmGLQOut (linObjectQuotientMatrix L) out ∧ cost ≤ VB) :=
    (linObjectNormal_spec hh hn h.quotient hjh hjs L (by omega) hfull).mono
      fun out cost ho' => ⟨ho'.1, ho'.2.trans (linPolyEnvelope_bound (linObjectNormalAllCost_poly hh hn)
        (Nat.zero_le _) hnormArg (Nat.zero_le _))⟩
  apply EvalAll.letE (normBound_call
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR, win]) (i := 7) rfl) hproduct)
  intro wn cw hwn
  obtain ⟨hwn, wwn, hcw⟩ := hwn
  apply EvalAll.letE (normBound_call
    (Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR, win, wn]) (i := 7) rfl) hquotient)
  intro vn cv hvn
  obtain ⟨hvn, wvn, hcv⟩ := hvn
  have dv (k : ℕ) {v : Val}
      (hv : [input, pv, encIntMatrix M, idsN, idsT, lv, idsR, win, wn, vn][k]? = some v) :=
    Det.var' (P := P) (env := [input, pv, encIntMatrix M, idsN, idsT, lv, idsR, win, wn, vn]) (i := k) hv
  have dout := Det.snoc (Det.mk4 (dv 1 rfl) (dv 2 rfl) (dv 7 rfl) (dv 8 rfl)) (dv 9 rfl)
  refine dout.post fun cost hcost => ⟨?_, ?_⟩
  · exact ⟨M, bss.map encGroup, L, wn, vn, rfl, hM, hgroups, hLC, hfull, hwn, hvn⟩
  · have wh := wt_list4_le pv (encIntMatrix M) win wn
    have wout := wt_list_le [pv, encIntMatrix M, win, wn, vn]
    have wctx := wt_list4_le (encGroup as) (encIntMatrix M) idsN idsT
    have wlocal := wt_list2_le ctx (.list (bss.map encGroup))
    have wwin := wt_list3_le idsR idsT lv
    have hpv : pv.wt ≤ PB := wp
    have hnat : n * n ≤ (W + 1) ^ 2 := by simpa only [pow_two] using hnPow
    have hnt := wt_nat_le as.length
    have hnr : N ≤ (W + 1) ^ 2 + 1 := by dsimp only [N]; omega
    change cn ≤ 2 * W + 0 + 5 + (0 + 3) + (Val.nat n).wt + 1 +
      (2 * W + 0 + 5 + (0 + 3) + (Val.nat n).wt + 1) + n * n + 3 + (1 + 3) + N + 3 + RB + idsN.wt + 1 at hcn
    change ct ≤ (encIntMatrix M).wt + 1 + as.length + 3 + RB + idsT.wt + 1 at hct
    simp only [List.length_map, List.length_finRange] at hcr
    change cr ≤ (encIntMatrix M).wt + 1 + as.length + 3 +
      (idsN.wt + 1 + N + 3) + (as.length + N) + 3 + RB + idsR.wt + 1 at hcr
    change ci ≤ idsR.wt + 1 + (idsT.wt + 1) + (lv.wt + 1) + 3 * win.wt + 8 at hci
    change cl ≤ 2 * W + 0 + 5 + ((encIntMatrix M).wt + 1) + (idsN.wt + 1) + (idsT.wt + 1) +
      4 * ctx.wt + 9 + (pv.wt + 1 + (1 + 3) + (Val.list (bss.map encGroup)).wt + 1) +
      2 * (Val.list [ctx, .list (bss.map encGroup)]).wt + 7 + 2 * LB + 1 at hcl
    simp only [List.cons_append, List.nil_append] at hcost ⊢
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at wout
    change _ ≤ 1000000 * ((W + 1) ^ 2 + W + PB + AB + RB + LB + WB + VB + 1)
    change idsN.wt ≤ RB at widN
    change idsT.wt ≤ RB at widT
    change idsR.wt ≤ RB at widR
    change lv.wt ≤ LB at wl
    change (encIntMatrix M).wt ≤ AB at wm
    change ctx.wt ≤ 2 * ((encGroup as).wt + (encIntMatrix M).wt + idsN.wt + idsT.wt) + 8 at wctx
    change win.wt ≤ 2 * (idsR.wt + idsT.wt + lv.wt) + 7 at wwin
    have scalar := linObjectDataTail_cost W ((W + 1) ^ 2) PB AB RB LB WB VB n as.length N cn ct cl cr ci cw cv cost
      (encGroup as).wt (encIntMatrix M).wt idsN.wt idsT.wt idsR.wt (Val.list (bss.map encGroup)).wt
      pv.wt lv.wt win.wt wn.wt vn.wt ctx.wt
      (Val.list [ctx,.list (bss.map encGroup)]).wt (Val.list [pv,encIntMatrix M,win,wn]).wt
      (Val.list [pv,encIntMatrix M,win,wn,vn]).wt (Val.nat n).wt
      rfl hnat hnr ht wa.le wm hn0 widN widT widR wg hpv wl wwn wvn wctx wwin
      hcn hct hcr hci hcl hcw hcv hcost wlocal wh
      (by simpa only [Nat.add_assoc, Nat.add_zero, Nat.reduceAdd] using wout)
    exact scalar

end GI.Impl
