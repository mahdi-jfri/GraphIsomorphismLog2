module

public import Workspace.Impl.VsHIsoOut

@[expose] public section

/-!
# The context of the hard case

From the hand-off value `vsPGIn s as Lb ccs tcs ys r` the program `vsHCtxE` builds the context
`vsPCtx I s.ws' (vsQCs s) (vsPRows p Lb) s.hs` of step 4 (`vsHCtx_spec`), as `vsPCtxE` does from
the input of step 4.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {I : VecStabInst}

/-- On the hand-off value: the context. -/
def vsHCtxE (flm rws rep : ℕ) : Expr :=
  .letE (.call flm (mk2 (.nat 0) (arg 10)))
    (.letE (.call rws (mk2 (.get (.get (arg 4) (.nat 0)) (.nat 0)) (.var 1)))
      (.letE (.call rep (mk2 (.arith .mul (.length (.get (.get (arg 4) (.nat 0)) (.nat 3)))
          (.length (.get (.get (arg 4) (.nat 0)) (.nat 3)))) (.nat 0)))
        (vsPMk7 (arg 0) (arg 4) (.get (.get (arg 4) (.nat 0)) (.nat 0)) (.var 2) (.var 3) (arg 1)
          (.get (.get (arg 0) (.nat 0)) (.nat 0)))))

set_option maxHeartbeats 4000000 in
/-- **The context program of the hard case.** -/
theorem vsHCtx_spec {P : Program} {f flm it fl rws rep : ℕ} (hf : P.funs[f]? = some (vsHCtxE flm rws rep))
    (hflm : P.HasAt flm (mapFuns flm it)) (hit : P.funs[it]? = some (vsPFlItemE fl))
    (hfl : P.HasAt fl (vsWFlatFuns fl)) (hrws : P.HasAt rws (vsWRowsFuns rws))
    (hrep : P.HasAt rep (replicateFuns rep))
    {s : VsQSt I} {N W : ℕ} (hpN : I.p ≤ N) (hDD : vsQD s * vsQD s ≤ N)
    {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {ccs tcs ys : List (Perm (Fin I.n))}
    {r : ℕ} (hLb : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (hLbl : Lb.length ≤ N)
    (hW : (vsPGIn s as Lb ccs tcs ys r).wt ≤ W) :
    FunDet P f (vsPGIn s as Lb ccs tcs ys r) (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs)
      (vsPCtxPCost N W) := by
  have hp0 := I.prime.pos
  set D := vsQD s
  have hDc : (vsQCs s).length = D := rfl
  set fr := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set vs := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, fr, encGroup as, encGroup ccs,
    Val.list (tcs.map encPerm), Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb]
  have eA : vsPGIn s as Lb ccs tcs ys r = .list vs := rfl
  rw [eA] at hW ⊢
  have a10 : Det P [Val.list vs] (arg 10) (.list (Lb.map vsWVs)) _ :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := 10) rfl
  -- flattening
  have hDN : D ≤ N := (Nat.le_mul_self D).trans hDD
  have hitem : ∀ M ∈ Lb, FunDet P it (.list [.nat 0, vsWVs M]) (natList M.flatten)
      (2 * 10 ^ 6 * (N + 1) ^ 4) := by
    intro M hM
    have d1 := Det.arg' (P := P) (vs := [Val.nat 0, vsWVs M]) (rest := []) (j := 1) rfl
    have dc := Det.call d1 (vsWFlat_spec hfl hpN hDD (hLb M hM))
    refine FunDet.intro hit (dc.mono ?_)
    have wM : (vsWVs M).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
      wt_vsWVs_le (fun u hu => ⟨fun y hy => ((hLb M hM).1 u hu).1 y hy |>.le.trans hpN,
        by rw [((hLb M hM).1 u hu).2]; exact hDN⟩) (by rw [(hLb M hM).2]; omega)
    have hfit := vsP_flatten_fit (hLb M hM)
    have wF := wt_natList_le_sq (B := N) (xs := M.flatten) (fun y hy => (hfit.1 y hy).le.trans hpN)
      (by rw [hfit.2]; exact hDD)
    have w2 := wt_list2_le (Val.nat 0) (vsWVs M)
    have := wt_nat_le 0
    have q1 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q2 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hmap := vsQ_map hflm (c := .nat 0) Lb vsWVs (fun M => natList M.flatten) vsWVs_injective hitem
  have eF : Val.list (Lb.map fun M => natList M.flatten) = vsWVs (Lb.map List.flatten) := by
    rw [vsWVs, List.map_map]; rfl
  rw [eF] at hmap
  have dF := Det.call (Det.mk2 (Det.nat (P := P) (env := [Val.list vs]) 0) a10) hmap
  -- rows
  set us := Lb.map List.flatten
  have hus : VsWFit I.p (D * D) us := by
    intro u hu
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hu
    exact vsP_flatten_fit (hLb M hM)
  have hul : us.length ≤ N := by rw [List.length_map]; exact hLbl
  set F4 := Val.list [Val.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]
  set E1 := [Val.list vs, vsWVs us]
  have bfr : Det P E1 (arg 4) fr _ := Det.arg' (P := P) (vs := vs) (rest := [vsWVs us]) (j := 4) rfl
  have bf0 : Det P E1 (.get (arg 4) (.nat 0)) F4 _ := Det.get' bfr (Det.nat 0) rfl
  have bp : Det P E1 (.get (.get (arg 4) (.nat 0)) (.nat 0)) (.nat I.p) _ :=
    Det.get' bf0 (Det.nat 0) rfl
  have dR := Det.call (Det.mk2 bp (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsWRows_spec hrws hp0 hpN hDD hus hul)
  -- zeros
  set E2 := [Val.list vs, vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val)]
  have cfr : Det P E2 (arg 4) fr _ :=
    Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val)])
      (j := 4) rfl
  have cf0 : Det P E2 (.get (arg 4) (.nat 0)) F4 _ := Det.get' cfr (Det.nat 0) rfl
  have cz : Det P E2 (.get (.get (arg 4) (.nat 0)) (.nat 3)) (natList (vsWZ (vsQCs s).length)) _ :=
    Det.get' cf0 (Det.nat 3) rfl
  have eZl : natList (vsWZ (vsQCs s).length) = .list ((vsWZ D).map Val.nat) := rfl
  rw [eZl] at cz
  have cD := Det.length cz
  rw [List.length_map, show (vsWZ D).length = D by simp [vsWZ]] at cD
  have cDD := Det.arith' (op := .mul) cD cD rfl
  have dZ := vsWZero_det hrep cDD (N := N) (by simp only [BinOp.eval]; exact hDD)
  -- the context
  set E3 := [Val.list vs, vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val),
    natList (vsWZ (BinOp.eval .mul D D))]
  have arg' : ∀ j (v : Val), vs[j]? = some v → Det P E3 (arg j) v (2 * (Val.list vs).wt + j + 5) :=
    fun j v h => Det.arg' (P := P) (vs := vs) (rest := [vsWVs us, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D))]) (j := j) h
  have eG := arg' 0 (vsQGam I) rfl
  have eH := arg' 1 (encGroup s.hs) rfl
  have eFr := arg' 4 fr rfl
  have eF0 : Det P E3 (.get (arg 4) (.nat 0)) F4 _ := Det.get' eFr (Det.nat 0) rfl
  have eP : Det P E3 (.get (.get (arg 4) (.nat 0)) (.nat 0)) (.nat I.p) _ :=
    Det.get' eF0 (Det.nat 0) rfl
  set Gm := Val.list [encGroup I.gs, vsQTable I, vsQE I.p I.d (vsQExp I) 1]
  set G2 := Val.list [Val.nat I.n, Val.list ((1 :: I.gs).map encPerm)]
  have eG' : Det P E3 (arg 0) Gm _ := eG
  have eG0 : Det P E3 (.get (arg 0) (.nat 0)) G2 _ := Det.get' eG' (Det.nat 0) rfl
  have eN : Det P E3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat I.n) _ :=
    Det.get' eG0 (Det.nat 0) rfl
  have dC := Det.vsPMk7 eG eFr eP (Det.var' (P := P) (env := E3) (i := 2) rfl)
    (Det.var' (P := P) (env := E3) (i := 3) rfl) eH eN
  have eC : Val.list [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n] =
      vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs := rfl
  rw [eC] at dC
  have dAll := Det.letE dF (Det.letE dR (Det.letE dZ dC))
  refine FunDet.intro hf (dAll.mono ?_)
  -- weights of the parts of the input
  have hm : ∀ v ∈ vs, v.wt < (Val.list vs).wt := fun v hv => wt_le_wt_list hv
  have w2 := hm (Val.list (Lb.map vsWVs)) (List.mem_iff_getElem?.2 ⟨10, rfl⟩)
  have w4 := hm fr (List.mem_iff_getElem?.2 ⟨4, rfl⟩)
  have w5 := hm (vsQGam I) (List.mem_iff_getElem?.2 ⟨0, rfl⟩)
  have w6 := hm (encGroup s.hs) (List.mem_iff_getElem?.2 ⟨1, rfl⟩)
  have w7 : F4.wt < fr.wt := wt_le_wt_list (by simp [fr, F4, vsWFrVal])
  have w8 : G2.wt < Gm.wt := wt_le_wt_list (by simp [Gm, G2, encGroup, encPerms])
  have w9 : (Val.nat I.p).wt < F4.wt := wt_le_wt_list (by simp [F4])
  have w10 : (Val.nat I.n).wt < G2.wt := wt_le_wt_list (by simp [G2])
  have wz3 : (natList (vsWZ (vsQCs s).length)).wt < F4.wt := wt_le_wt_list (by simp [F4])
  have eZl' : (Val.list ((vsWZ D).map Val.nat)).wt = (natList (vsWZ (vsQCs s).length)).wt := rfl
  have eGm : (vsQGam I).wt = Gm.wt := rfl
  have wDv := wt_nat_le D
  -- weights of the computed parts
  have hRf := vsWRows_fits hp0 hpN hDD hus
  have wR : (Val.list ((vsWRows I.p us).map VsRow.val)).wt ≤ 81 * (N + 1) ^ 3 + 4 :=
    wt_vsRows_le hRf.rows (by
      have := hRf.nrows
      have e : (vsWRows I.p us).length = (vsInsertAll I.p (vsWPairs us)).1.length := rfl
      omega)
  have hUB : VsWBnd N us := fun u hu => ⟨fun y hy => ((hus u hu).1 y hy).le.trans hpN,
    by rw [(hus u hu).2]; exact hDD⟩
  have wU : (vsWVs us).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsWVs_le hUB (by omega)
  have wZ : (natList (vsWZ (BinOp.eval .mul D D))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ, BinOp.eval]; omega)
  have hDDv : BinOp.eval .mul D D ≤ N := by simp only [BinOp.eval]; exact hDD
  have w7l := wt_list_le [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
      natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w7l
  have eCtx : (vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs).wt =
      (Val.list [vsQGam I, fr, .nat I.p, Val.list ((vsWRows I.p us).map VsRow.val),
        natList (vsWZ (BinOp.eval .mul D D)), encGroup s.hs, .nat I.n]).wt := rfl
  have w0l := wt_list2_le (Val.nat 0) (Val.list (Lb.map vsWVs))
  have wpu := wt_list2_le (Val.nat I.p) (vsWVs us)
  have wDD := wt_nat_le (BinOp.eval .mul D D)
  have wz0 := wt_nat_le 0
  have hLbM : Lb.length * (2 * 10 ^ 6 * (N + 1) ^ 4) ≤ (N + 1) * (2 * 10 ^ 6 * (N + 1) ^ 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  set Y := (N + 1) * (W + 100 * (N + 1) ^ 3)
  have hY1 : W + 100 * (N + 1) ^ 3 ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hM : mapK * (Lb.length + 1) * ((Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt +
      (vsWVs us).wt + 1) ≤ 1000 * (2 * Y) := by
    have hA : (Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt + (vsWVs us).wt + 1 ≤
        2 * (W + 100 * (N + 1) ^ 3) := by omega
    have e1 : (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) = 2 * Y := by simp only [Y]; ring
    calc mapK * (Lb.length + 1) * ((Val.list [Val.nat 0, Val.list (Lb.map vsWVs)]).wt +
          (vsWVs us).wt + 1) ≤ mapK * (N + 1) * (2 * (W + 100 * (N + 1) ^ 3)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hA
      _ = 1000 * (2 * Y) := by rw [mul_assoc, e1]; rfl
  have eY : 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 3) = 10 ^ 4 * Y := by rw [mul_assoc]
  unfold vsPCtxPCost
  rw [eY]
  omega

end GI.Impl
