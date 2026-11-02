import Workspace.Impl.VsWProgFrame
import Workspace.Proved.VsWFrameLoc

/-!
# Coordinates, local matrices and lifts as programs

All three take a frame value `fr = vsWFrVal p d ws' cs` (see `Impl/VsWProgFrame.lean`) as
their first argument.

* `vsWCoFuns b` (13 functions), `vsWCo_spec`: on `[fr, natList x]` the local coordinates
  `natList (vsWCo p ws' cs x)`. Meaning: `GI.Proved.vsWCo_sub`, `GI.Proved.vsWCo_unique`.
* `vsWLocFuns b` (33 functions), `vsWLoc_spec`: on `[fr, vsWVs A]` the local matrix
  `vsWVs (vsWLoc p d ws' cs A)`. Meaning: `GI.Proved.vsWLoc_co`.
* `vsWLiftFuns b` (20 functions), `vsWLift_spec`: on `[fr, vsWVs us]` the lift
  `vsWVs (vsWLift p d ws' cs us)`. Meaning: `GI.Proved.vsWLift_span`, `GI.Proved.vsWLift_mem`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- Entry `j` of the header of a frame. -/
def vsWFrH (j : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat j)

theorem vsWFrA_det {P : Program} {p d : ℕ} {ws' cs : List (List ℕ)} {y : Val} {rest : List Val} :
    Det P (.list [vsWFrVal p d ws' cs, y] :: rest) (arg 0)
      (.list [.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)], vsWVs ws',
        vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
      (2 * (Val.list [vsWFrVal p d ws' cs, y]).wt + 0 + 5) :=
  Det.arg' (P := P) (rest := rest) (vs := [vsWFrVal p d ws' cs, y]) (j := 0) rfl

theorem vsWFrH_det {P : Program} {p d : ℕ} {ws' cs : List (List ℕ)} {y : Val} {rest : List Val}
    {j : ℕ} {v : Val}
    (hv : [Val.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)][j]? = some v) :
    Det P (.list [vsWFrVal p d ws' cs, y] :: rest) (vsWFrH j) v
      (2 * (Val.list [vsWFrVal p d ws' cs, y]).wt + 0 + 5 + (0 + 3) +
        (Val.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)]).wt + 1 +
        (j + 3) + v.wt + 1) :=
  Det.get' (Det.get' (vsWFrA_det (P := P) (y := y) (rest := rest)) (Det.nat 0)
    (vs := [Val.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)], vsWVs ws',
        vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)]) rfl) (Det.nat j) hv

/-- Part `j` of a frame. -/
theorem vsWFrL_det {P : Program} {p d : ℕ} {ws' cs : List (List ℕ)} {y : Val} {rest : List Val}
    {j : ℕ} {v : Val}
    (hv : [Val.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)], vsWVs ws',
      vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)][j]? = some v) :
    Det P (.list [vsWFrVal p d ws' cs, y] :: rest) (.get (arg 0) (.nat j)) v
      (2 * (Val.list [vsWFrVal p d ws' cs, y]).wt + 0 + 5 + (j + 3) + v.wt + 1) :=
  Det.get' (vsWFrA_det (P := P) (y := y) (rest := rest)) (Det.nat j) hv

/-! ### Coordinates -/

/-- The coordinates, on `[fr, x]`: sift `(x, 0)` through the frame rows, negate the tag. -/
def vsWCoF (sft lin : ℕ) : Expr :=
  .letE (.call sft (mk3 (vsWFrH 0) (.get (arg 0) (.nat 3)) (mk2 (arg 1) (vsWFrH 3))))
    (.call lin (.snoc (mk4 (vsWFrH 0) (.arith .sub (vsWFrH 0) (.nat 1)) (.nat 0)
      (.get (.var 1) (.nat 1))) (.get (.var 1) (.nat 1))))

/-- The coordinates program at base `b` (13 functions). -/
def vsWCoFuns (b : ℕ) : List Expr :=
  [vsWCoF (b + 1) (b + 5)] ++ vsSiftFuns (b + 1) (b + 4) ++ [vsSiftStepF (b + 5)] ++
    vsLinFuns (b + 5)

theorem vsWCoFuns_length (b : ℕ) : (vsWCoFuns b).length = 13 := rfl

/-- **The coordinates program.** -/
theorem vsWCo_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWCoFuns b)) {p N d : ℕ}
    {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) {x : List ℕ}
    (hx : GI.Proved.VsWFit p d [x]) :
    FunDet P b (.list [vsWFrVal p d ws' cs, natList x]) (natList (vsWCo p ws' cs x))
      (10 ^ 7 * (N + 1) ^ 4) := by
  have H' := H
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := H'
  have h0 : P.funs[b]? = some (vsWCoF (b + 1) (b + 5)) := h.get (j := 0) (by simp [vsWCoFuns])
  have hs : P.HasAt (b + 1) (vsSiftFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsSiftStepF (b + 5)) :=
    h.get (j := 4) (by rw [vsWCoFuns_length]; omega)
  have hli : P.HasAt (b + 5) (vsLinFuns (b + 5)) := h.block 5 rfl
  obtain ⟨hxp, hxl⟩ := hx x (List.mem_singleton_self _)
  set A := Val.list [vsWFrVal p d ws' cs, natList x]
  have hfit := vsWFrRows_fits H
  have hP : VsPairFits p N (x, vsWZ cs.length) :=
    ⟨hxp, fun y hy => by simp [vsWZ] at hy; omega, by simp; omega, by simp [vsWZ]; omega⟩
  have hr : ∀ r ∈ (vsWFrRows p ws' cs), VsRowFits N (x, vsWZ cs.length).1.length (x, vsWZ cs.length).2.length r := by
    intro r hr0
    have := hfit.rows r hr0
    simpa [hxl, vsWZ] using this
  have hrl : (vsWFrRows p ws' cs).length ≤ N := hfit.nrows.trans (by omega)
  have g0 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := natList x) (rest := []) (j := 0)
    (p := p) (d := d) rfl
  have g3 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := natList x) (rest := []) (j := 3)
    (p := p) (d := d) rfl
  have gR := vsWFrL_det (P := P) (ws' := ws') (cs := cs) (y := natList x) (rest := []) (j := 3)
    (p := p) (d := d) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [vsWFrVal p d ws' cs, natList x]) (j := 1) rfl
  have dS := Det.call (Det.mk3 g0 gR (Det.mk2 a1 g3)) (vsSift_spec hs hst hli (by omega) hpN hP hr hrl)
  set S := vsSift p (vsWFrRows p ws' cs) (x, vsWZ cs.length)
  have hSf := vsSift_fits (by omega) (vsWFrRows p ws' cs) hP
  obtain ⟨l1, l2⟩ := vsSift_length p (vsWFrRows p ws' cs) (x, vsWZ cs.length)
  -- the body
  set SV := vsPairVal S
  have k0 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := natList x) (rest := [SV]) (j := 0)
    (p := p) (d := d) rfl
  have dsub := Det.arith' k0 (Det.nat 1) (op := .sub) rfl
  have vS : Det P [A, SV] (.var 1) SV _ := Det.var' rfl
  have dT := Det.get' vS (Det.nat 1) (show [natList S.1, natList S.2][1]? = some (natList S.2) from rfl)
  have d5 := Det.snoc (Det.mk4 k0 dsub (Det.nat 0) dT) dT
  simp only [List.cons_append, List.nil_append] at d5
  have hlt : ∀ y ∈ S.2, y ≤ N := fun y hy => (hSf.ht y hy).le.trans hpN
  have hSl : S.2.length = cs.length := by rw [l2]; simp [vsWZ]
  have dlin := Det.call d5 (vsLin_spec hli (p := p) (a := p - 1) (b := 0) (N := N) (by omega) hlt hlt
    (by omega) (by omega) le_rfl hpN (by omega) (by omega))
  have e1 : vsLin p (p - 1) 0 S.2 S.2 = vsWCo p ws' cs x := rfl
  rw [e1] at dlin
  refine FunDet.intro h0 ((Det.letE dS dlin).mono ?_)
  have wF := wt_vsWFrVal_le H
  have eF : vsWFrVal p d ws' cs = .list [.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)] := rfl
  have wH := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)]) (by simp)
  have wRw := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list ((vsWFrRows p ws' cs).map VsRow.val)) (by simp)
  rw [← eF] at wH wRw
  have wx : (natList x).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => (hxp y hy).le.trans hpN) (by omega)
  have wz : (natList (vsWZ cs.length)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wA := wt_list2_le (vsWFrVal p d ws' cs) (natList x)
  have eA : A.wt = (Val.list [vsWFrVal p d ws' cs, natList x]).wt := rfl
  have wAS := wt_list2_le A SV
  have wSV : SV.wt ≤ 20 * (N + 1) ^ 2 + 6 := wt_vsPairVal_le hpN hSf.hx hSf.ht hSf.lx hSf.lt
  have wT : (natList S.2).wt < SV.wt := wt_le_wt_list (by simp [SV])
  have wp := wt_nat_le p
  have wp1 := wt_nat_le (p - 1)
  have w00 := wt_nat_le 0
  have w01 := wt_nat_le 1
  have hsub : GI.Machine.BinOp.sub.eval p 1 = p - 1 := rfl
  have wP2 := wt_list2_le (natList x) (natList (vsWZ cs.length))
  have wP3 := wt_list3_le (.nat p) (.list ((vsWFrRows p ws' cs).map VsRow.val)) (.list [natList x, natList (vsWZ cs.length)])
  have eSA : vsSiftArg p (vsWFrRows p ws' cs) (x, vsWZ cs.length) =
    .list [.nat p, .list ((vsWFrRows p ws' cs).map VsRow.val), .list [natList x, natList (vsWZ cs.length)]] := rfl
  have w5 := wt_list_le [Val.nat p, .nat (p - 1), .nat 0, natList S.2, natList S.2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w5
  have eL : vsLinArg p (p - 1) 0 S.2 S.2 =
    .list [.nat p, .nat (p - 1), .nat 0, natList S.2, natList S.2] := rfl
  have w4 := wt_list4_le (.nat p) (.nat (p - 1)) (.nat 0) (natList S.2)
  have wo : (natList (vsWCo p ws' cs x)).wt ≤ 5 * (N + 1) ^ 2 := by
    rw [← e1]
    exact wt_natList_le_sq (fun y hy => by
      have := vsLin_lt (p := p) (a := p - 1) (b := 0) (by omega) S.2 S.2 y hy
      omega) (by rw [vsLin_length]; omega)
  have q0 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [eSA, eL, hsub] at *
  omega

/-! ### Local matrices -/

/-- The local matrix, on `[fr, A]`: the coordinates of the images of the complement basis. -/
def vsWLocF (mp mm : ℕ) : Expr :=
  .call mp (mk2 (arg 0) (.call mm (mk2 (mk3 (vsWFrH 0) (arg 1) (vsWFrH 2)) (.get (arg 0) (.nat 2)))))

/-- The local matrix program at base `b` (33 functions). -/
def vsWLocFuns (b : ℕ) : List Expr :=
  [vsWLocF (b + 1) (b + 17)] ++ mapFuns (b + 1) (b + 4) ++ vsWCoFuns (b + 4) ++
    vsFMatMulFuns (b + 17)

theorem vsWLocFuns_length (b : ℕ) : (vsWLocFuns b).length = 33 := rfl

/-- **The local matrix program.** -/
theorem vsWLoc_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWLocFuns b)) {p N d : ℕ}
    {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) {A : List (List ℕ)}
    (hA : GI.Proved.VsWSq p d A) :
    FunDet P b (.list [vsWFrVal p d ws' cs, vsWVs A]) (vsWVs (vsWLoc p d ws' cs A))
      (2 * 10 ^ 10 * (N + 1) ^ 5) := by
  have H' := H
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := H'
  have h0 : P.funs[b]? = some (vsWLocF (b + 1) (b + 17)) := h.get (j := 0) (by simp [vsWLocFuns])
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hco : P.HasAt (b + 4) (vsWCoFuns (b + 4)) := h.block 4 rfl
  have hmm : P.HasAt (b + 17) (vsFMatMulFuns (b + 17)) := h.block 17 rfl
  set X := Val.list [vsWFrVal p d ws' cs, vsWVs A]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [vsWFrVal p d ws' cs, vsWVs A]) (j := 0) rfl
  have a1 : Det P [X] (arg 1) (.list (A.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [vsWFrVal p d ws' cs, vsWVs A]) (j := 1) rfl
  have g0 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs A) (rest := []) (j := 0)
    (p := p) (d := d) rfl
  have g2 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs A) (rest := []) (j := 2)
    (p := p) (d := d) rfl
  have gC : Det P [X] (.get (arg 0) (.nat 2)) (.list (cs.map natList)) _ :=
    vsWFrL_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs A) (rest := []) (j := 2)
      (p := p) (d := d) rfl
  have hAl : A.length = d := hA.2
  have HB : VsFMatFits p N A (vsWZ d) :=
    ⟨fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
      fun r hr y hy => ((hA.1 r hr).1 y hy).le.trans hpN, fun r hr => (hA.1 r hr).2.le.trans hdN,
      fun r hr => by simp [vsWZ, (hA.1 r hr).2], by omega⟩
  have HA : ∀ a ∈ cs, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ A.length ≤ a.length :=
    fun a ha => ⟨(hc a ha).1, (hc a ha).2.le.trans hdN, by rw [hAl, (hc a ha).2]⟩
  have dmm := Det.call (Det.mk2 (Det.mk3 g0 a1 g2) gC) (vsFMatMul_spec hmm (by omega) hpN HB HA
    (by omega))
  have e1 : (cs.map fun a => natList (vsFRowMul p a A (vsWZ d))) = (vsWImg p d A cs).map natList := by
    simp [vsWImg]
  rw [e1] at dmm
  have hIf := vsWImg_fit' (p := p) (d := d) (by omega) A cs
  have dmap := vsQ_map hmp (vsWImg p d A cs) natList (fun y => natList (vsWCo p ws' cs y))
    vsQ_natList_injective (c := vsWFrVal p d ws' cs) fun y hy =>
      vsWCo_spec hco H (fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact hIf _ hy)
  have e2 : (vsWImg p d A cs).map (fun y => natList (vsWCo p ws' cs y)) =
      (vsWLoc p d ws' cs A).map natList := by simp [vsWLoc]
  rw [e2] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 a0 dmm) dmap).mono ?_)
  have wF := wt_vsWFrVal_le H
  have eF : vsWFrVal p d ws' cs = .list [.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)] := rfl
  have wH := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)]) (by simp)
  have wCs := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := vsWVs cs) (by simp)
  rw [← eF] at wH wCs
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hdN) (show A.length ≤ N + 1 by omega)
  have wI := wt_vsWVs_le (VsWFit.bnd hIf hpN hdN) (show (vsWImg p d A cs).length ≤ N + 1 by
    simp [vsWImg]; omega)
  have hLf := GI.Proved.vsWLoc_fit (p := p) (d := d) (by omega) ws' cs A
  have wL := wt_vsWVs_le (VsWFit.bnd hLf.1 hpN (show cs.length ≤ N by omega))
    (show (vsWLoc p d ws' cs A).length ≤ N + 1 by rw [hLf.2]; omega)
  have eA : (vsWVs A).wt = (Val.list (A.map natList)).wt := rfl
  have eC : (vsWVs cs).wt = (Val.list (cs.map natList)).wt := rfl
  have eI : (vsWVs (vsWImg p d A cs)).wt = (Val.list ((vsWImg p d A cs).map natList)).wt := rfl
  have eL : (vsWVs (vsWLoc p d ws' cs A)).wt = (Val.list ((vsWLoc p d ws' cs A).map natList)).wt := rfl
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wX := wt_list2_le (vsWFrVal p d ws' cs) (vsWVs A)
  have eX : X.wt = (Val.list [vsWFrVal p d ws' cs, vsWVs A]).wt := rfl
  have w3 := wt_list3_le (.nat p) (.list (A.map natList)) (natList (vsWZ d))
  have eCtx : vsFMatCtx p A (vsWZ d) = .list [.nat p, .list (A.map natList), natList (vsWZ d)] := rfl
  have w2 := wt_list2_le (vsFMatCtx p A (vsWZ d)) (.list (cs.map natList))
  have w2' := wt_list2_le (vsWFrVal p d ws' cs) (.list ((vsWImg p d A cs).map natList))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := (vsWImg p d A cs).length) (B := 10 ^ 7 * (N + 1) ^ 4)
    (c := 10 ^ 7) (k := 4)
    (W := (Val.list [vsWFrVal p d ws' cs, .list ((vsWImg p d A cs).map natList)]).wt +
      (Val.list ((vsWLoc p d ws' cs A).map natList)).wt) (by simp [vsWImg]; omega) le_rfl (by omega)
  have e5 : (N + 1) ^ (4 + 1) = (N + 1) ^ 5 := rfl
  rw [e5] at kmap
  rw [eCtx] at w2
  omega

/-! ### Lifts -/

/-- The lift, on `[fr, us]`: `ws'` followed by the combinations of the complement basis. -/
def vsWLiftF (app mm : ℕ) : Expr :=
  .call app (mk2 (.get (arg 0) (.nat 1))
    (.call mm (mk2 (mk3 (vsWFrH 0) (.get (arg 0) (.nat 2)) (vsWFrH 2)) (arg 1))))

/-- The lift program at base `b` (20 functions). -/
def vsWLiftFuns (b : ℕ) : List Expr :=
  [vsWLiftF (b + 1) (b + 4)] ++ appendFuns (b + 1) ++ vsFMatMulFuns (b + 4)

theorem vsWLiftFuns_length (b : ℕ) : (vsWLiftFuns b).length = 20 := rfl

/-- **The lift program.** -/
theorem vsWLift_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWLiftFuns b)) {p N d : ℕ}
    {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p cs.length us) (hl2 : ws'.length + us.length ≤ N) :
    FunDet P b (.list [vsWFrVal p d ws' cs, vsWVs us]) (vsWVs (vsWLift p d ws' cs us))
      (10 ^ 7 * (N + 1) ^ 5) := by
  have H' := H
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := H'
  have h0 : P.funs[b]? = some (vsWLiftF (b + 1) (b + 4)) := h.get (j := 0) (by simp [vsWLiftFuns])
  have happ : P.HasAt (b + 1) (appendFuns (b + 1)) := h.block 1 rfl
  have hmm : P.HasAt (b + 4) (vsFMatMulFuns (b + 4)) := h.block 4 rfl
  set X := Val.list [vsWFrVal p d ws' cs, vsWVs us]
  have a1 : Det P [X] (arg 1) (.list (us.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [vsWFrVal p d ws' cs, vsWVs us]) (j := 1) rfl
  have g0 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs us) (rest := []) (j := 0)
    (p := p) (d := d) rfl
  have g2 := vsWFrH_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs us) (rest := []) (j := 2)
    (p := p) (d := d) rfl
  have gC : Det P [X] (.get (arg 0) (.nat 2)) (.list (cs.map natList)) _ :=
    vsWFrL_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs us) (rest := []) (j := 2)
      (p := p) (d := d) rfl
  have gW : Det P [X] (.get (arg 0) (.nat 1)) (.list (ws'.map natList)) _ :=
    vsWFrL_det (P := P) (ws' := ws') (cs := cs) (y := vsWVs us) (rest := []) (j := 1)
      (p := p) (d := d) rfl
  have HB : VsFMatFits p N cs (vsWZ d) :=
    ⟨fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
      fun r hr y hy => ((hc r hr).1 y hy).le.trans hpN, fun r hr => (hc r hr).2.le.trans hdN,
      fun r hr => by simp [vsWZ, (hc r hr).2], by omega⟩
  have HA : ∀ a ∈ us, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ cs.length ≤ a.length :=
    fun a ha => ⟨(hus a ha).1, by rw [(hus a ha).2]; omega, (hus a ha).2.ge⟩
  have dmm := Det.call (Det.mk2 (Det.mk3 g0 gC g2) a1) (vsFMatMul_spec hmm (by omega) hpN HB HA
    (by omega))
  set ys := us.map fun a => natList (vsFRowMul p a cs (vsWZ d))
  have eV : Val.list (ws'.map natList ++ ys) = vsWVs (vsWLift p d ws' cs us) := by
    simp [vsWLift, vsWVs, ys]
  have hLf : GI.Proved.VsWFit p d (vsWLift p d ws' cs us) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h' x hx
    · exact vsWImg_fit' (p := p) (d := d) (by omega) cs us x hx
  have wLi := wt_vsWVs_le (VsWFit.bnd hLf hpN hdN) (show (vsWLift p d ws' cs us).length ≤ N + 1 by
    simp [vsWLift]; omega)
  have hK : loopModK = 1000 := rfl
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have wws' := wt_vsWVs_le (VsWFit.bnd h' hpN hdN) (show ws'.length ≤ N + 1 by omega)
  have eW : (vsWVs ws').wt = (Val.list (ws'.map natList)).wt := rfl
  have wI := wt_vsWVs_le (VsWFit.bnd (vsWImg_fit' (p := p) (d := d) (by omega) cs us) hpN hdN)
    (show (vsWImg p d cs us).length ≤ N + 1 by simp [vsWImg]; omega)
  have eI : (vsWVs (vsWImg p d cs us)).wt = (Val.list ys).wt := by simp [vsWVs, vsWImg, ys, Function.comp_def]
  have kapp : loopModK * (ys.length + 1) * ((Val.list [.list (ws'.map natList), .list ys]).wt +
      ys.length + (Val.list (ws'.map natList ++ ys)).wt + 1) ≤ 10 ^ 5 * (N + 1) ^ 4 := by
    have w2 := wt_list2_le (.list (ws'.map natList)) (.list ys)
    have hys : ys.length ≤ N := by simp [ys]; omega
    rw [eV, hK]
    calc 1000 * (ys.length + 1) * ((Val.list [.list (ws'.map natList), .list ys]).wt +
          ys.length + (vsWVs (vsWLift p d ws' cs us)).wt + 1)
        ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 10 ^ 5 * (N + 1) ^ 4 := by ring
  have dapp := Det.call (Det.mk2 gW dmm) ((append_spec happ _ _).mono fun w c hw =>
    ⟨hw.1, hw.2.trans (hw.1 ▸ kapp)⟩)
  rw [eV] at dapp
  refine FunDet.intro h0 (dapp.mono ?_)
  have wF := wt_vsWFrVal_le H
  have eF : vsWFrVal p d ws' cs = .list [.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)] := rfl
  have wH := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)]) (by simp)
  rw [← eF] at wH
  have wus := wt_vsWVs_le (N := N) (us := us)
    (fun u hu => ⟨fun y hy => ((hus u hu).1 y hy).le.trans hpN, by rw [(hus u hu).2]; omega⟩)
    (show us.length ≤ N + 1 by omega)
  have wcs := wt_vsWVs_le (VsWFit.bnd hc hpN hdN) (show cs.length ≤ N + 1 by omega)
  have eU : (vsWVs us).wt = (Val.list (us.map natList)).wt := rfl
  have eC : (vsWVs cs).wt = (Val.list (cs.map natList)).wt := rfl
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wX := wt_list2_le (vsWFrVal p d ws' cs) (vsWVs us)
  have eX : X.wt = (Val.list [vsWFrVal p d ws' cs, vsWVs us]).wt := rfl
  have w3 := wt_list3_le (.nat p) (.list (cs.map natList)) (natList (vsWZ d))
  have eCtx : vsFMatCtx p cs (vsWZ d) = .list [.nat p, .list (cs.map natList), natList (vsWZ d)] :=
    rfl
  have w2 := wt_list2_le (vsFMatCtx p cs (vsWZ d)) (.list (us.map natList))
  have w2' := wt_list2_le (.list (ws'.map natList)) (.list ys)
  rw [eCtx] at w2
  omega

end GI.Impl
