module

public import Workspace.Impl.VsWProgComp

@[expose] public section

/-!
# Frames as programs

A frame for `W' ≤ W` is given by a spanning list `ws'` of `W'` and a complement basis `cs`.
Its value `vsWFrVal p d ws' cs` holds `p`, `d`, the zero vectors of lengths `d` and
`D = cs.length`, the lists `ws'` and `cs`, and the echelon rows `vsWFrRows p ws' cs` used for
coordinates.

* `vsWFrRowsFuns b` (46 functions), `vsWFrRows_spec`: on `[p, vsWVs ws', vsWVs cs]` the rows.
* `vsWFrameFuns b` (95 functions), `vsWFrame_spec`: on `[p, d, vsWVs ws', vsWVs ws]` the frame
  value `vsWFrVal p d ws' (vsWComp p ws' ws)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The value of a frame. -/
def vsWFrVal (p d : ℕ) (ws' cs : List (List ℕ)) : Val :=
  .list [.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)], vsWVs ws', vsWVs cs,
    .list ((vsWFrRows p ws' cs).map VsRow.val)]

/-- The size hypotheses of a frame. -/
structure VsWFrOK (p N d : ℕ) (ws' cs : List (List ℕ)) : Prop where
  hp : 1 < p
  hpN : p ≤ N
  hdN : d ≤ N
  h' : GI.Proved.VsWFit p d ws'
  hc : GI.Proved.VsWFit p d cs
  hl : ws'.length + cs.length ≤ N

theorem vsW_wt_append_le (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ (Val.list xs).wt + (Val.list ys).wt := by
  rw [wt_list_eq, wt_list_eq, wt_list_eq]
  simp only [List.map_append, List.sum_append, List.length_append]
  have := GI.Machine.len_add_le_add xs.length ys.length
  have := GI.Machine.len_add_le_add (xs.map Val.size).sum (ys.map Val.size).sum
  omega

/-- `[z, w] ↦ (w, z)`. -/
def vsWFrPairF : Expr := mk2 (arg 1) (arg 0)

theorem vsWFrPair_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWFrPairF) {N : ℕ}
    {z w : List ℕ} (hz : (natList z).wt ≤ 5 * (N + 1) ^ 2) (hw : (natList w).wt ≤ 5 * (N + 1) ^ 2) :
    FunDet P f (.list [natList z, natList w]) (vsPairVal (w, z)) (200 * (N + 1) ^ 2 + 100) := by
  refine FunDet.intro hf ((Det.mk2
    (Det.arg' (P := P) (rest := []) (vs := [natList z, natList w]) (j := 1) rfl)
    (Det.arg' (P := P) (rest := []) (vs := [natList z, natList w]) (j := 0) rfl)).mono ?_)
  have := wt_list2_le (natList z) (natList w)
  have := wt_list2_le (natList w) (natList z)
  omega

/-- The frame rows, on `[p, ws', cs]`. -/
def vsWFrRowsF (rep app mp up ins : ℕ) : Expr :=
  .get (.call ins (mk3 (arg 0)
    (.call app (mk2 (.call mp (mk2 (.call rep (mk2 (.length (arg 2)) (.nat 0))) (arg 1)))
      (.call up (mk2 (.length (arg 2)) (arg 2)))))
    (mk2 .nil .nil))) (.nat 0)

/-- The frame rows program at base `b` (46 functions). -/
def vsWFrRowsFuns (b : ℕ) : List Expr :=
  [vsWFrRowsF (b + 1) (b + 4) (b + 7) (b + 11) (b + 17)] ++ replicateFuns (b + 1) ++
    appendFuns (b + 4) ++ mapFuns (b + 7) (b + 10) ++ [vsWFrPairF] ++ vsUnitPairsFuns (b + 11) ++
    vsInsertAllFuns (b + 17)

theorem vsWFrRowsFuns_length (b : ℕ) : (vsWFrRowsFuns b).length = 46 := rfl

theorem vsWFrRows_fits {p N d : ℕ} {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) :
    VsAccFits p N d cs.length (ws'.length + cs.length) (vsInsertAll p (vsWFrPairs ws' cs)) := by
  have hok := GI.Proved.vsWFrPairs_ok H.hp H.h' H.hc
  have := vsInsertAll_fits (by have := H.hp; omega) H.hpN (L := vsWFrPairs ws' cs) (lx := d)
    (lt := cs.length) (fun xt hxt => by
      obtain ⟨h1, h2, h3, h4⟩ := hok xt hxt
      exact ⟨⟨h1, h2, by have := H.hdN; omega, by have := H.hl; omega⟩, h3, h4⟩)
  simpa [vsWFrPairs, vsUnitPairs] using this

/-- **The frame rows program.** -/
theorem vsWFrRows_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWFrRowsFuns b)) {p N d : ℕ}
    {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) :
    FunDet P b (.list [.nat p, vsWVs ws', vsWVs cs]) (.list ((vsWFrRows p ws' cs).map VsRow.val))
      (4 * 10 ^ 7 * (N + 1) ^ 5) := by
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := H
  have h0 : P.funs[b]? = some (vsWFrRowsF (b + 1) (b + 4) (b + 7) (b + 11) (b + 17)) :=
    h.get (j := 0) (by simp [vsWFrRowsFuns])
  have hrep : P.HasAt (b + 1) (replicateFuns (b + 1)) := h.block 1 rfl
  have happ : P.HasAt (b + 4) (appendFuns (b + 4)) := h.block 4 rfl
  have hm : P.HasAt (b + 7) (mapFuns (b + 7) (b + 10)) := h.block 7 rfl
  have hpr : P.funs[b + 10]? = some vsWFrPairF := h.get (j := 10) (by rw [vsWFrRowsFuns_length]; omega)
  have hup : P.HasAt (b + 11) (vsUnitPairsFuns (b + 11)) := h.block 11 rfl
  have hin : P.HasAt (b + 17) (vsInsertAllFuns (b + 17)) := h.block 17 rfl
  set X := Val.list [.nat p, vsWVs ws', vsWVs cs]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs cs]) (j := 0) rfl
  have a1 : Det P [X] (arg 1) (.list (ws'.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs cs]) (j := 1) rfl
  have a2 : Det P [X] (arg 2) (.list (cs.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs ws', vsWVs cs]) (j := 2) rfl
  have dl := Det.length a2
  rw [List.length_map] at dl
  have hcN : cs.length ≤ N := by omega
  have dz := vsWZero_det hrep dl hcN
  have wz : (natList (vsWZ cs.length)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wu : ∀ u ∈ ws', (natList u).wt ≤ 5 * (N + 1) ^ 2 := fun u hu =>
    wt_natList_le_sq (fun y hy => ((h' u hu).1 y hy).le.trans hpN) ((h' u hu).2.le.trans hdN)
  have dmap := vsQ_map hm ws' natList (fun w => vsPairVal (w, vsWZ cs.length)) vsQ_natList_injective
    (c := natList (vsWZ cs.length)) fun w hw => vsWFrPair_spec hpr wz (wu w hw)
  have dm := Det.call (Det.mk2 dz a1) dmap
  have hvs : ∀ v ∈ cs, (∀ y ∈ v, y < p) ∧ v.length ≤ N :=
    fun v hv => ⟨(hc v hv).1, (hc v hv).2.le.trans hdN⟩
  have dup := Det.call (Det.mk2 dl a2) (vsWUP_spec hup hp1 hpN hcN hvs hcN)
  have wmp : (Val.list (ws'.map fun w => vsPairVal (w, vsWZ cs.length))).wt ≤ 100 * (N + 1) ^ 3 := by
    have := vs_wt_list_le_of (ws'.map fun w => vsPairVal (w, vsWZ cs.length))
      (c := 20 * (N + 1) ^ 2 + 6) (by
        simp only [List.mem_map, forall_exists_index, and_imp]
        rintro _ w hw rfl
        exact wt_vsPairVal_le hpN (h' w hw).1 (fun y hy => by simp [vsWZ] at hy; omega)
          ((h' w hw).2.le.trans hdN) (by simp [vsWZ]; omega))
    simp only [List.length_map] at this
    have e : ws'.length * (2 * (20 * (N + 1) ^ 2 + 6) + 1) ≤ (N + 1) * (60 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
    have : (N + 1) * (60 * (N + 1) ^ 2) = 60 * (N + 1) ^ 3 := by ring
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have wup := wt_vsWUP_le hp1 hpN hcN hvs hcN
  have eL : ws'.map (fun w => vsPairVal (w, vsWZ cs.length)) ++
      (vsUnitPairs cs.length cs).map vsPairVal = (vsWFrPairs ws' cs).map vsPairVal := by
    simp [vsWFrPairs]
  have wL : (Val.list ((vsWFrPairs ws' cs).map vsPairVal)).wt ≤ 300 * (N + 1) ^ 3 := by
    rw [← eL]
    have := vsW_wt_append_le (ws'.map fun w => vsPairVal (w, vsWZ cs.length))
      ((vsUnitPairs cs.length cs).map vsPairVal)
    omega
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have kapp : loopModK * (((vsUnitPairs cs.length cs).map vsPairVal).length + 1) *
      ((Val.list [.list (ws'.map fun w => vsPairVal (w, vsWZ cs.length)),
        .list ((vsUnitPairs cs.length cs).map vsPairVal)]).wt +
        ((vsUnitPairs cs.length cs).map vsPairVal).length +
        (Val.list (ws'.map (fun w => vsPairVal (w, vsWZ cs.length)) ++
          (vsUnitPairs cs.length cs).map vsPairVal)).wt + 1) ≤ 10 ^ 6 * (N + 1) ^ 4 := by
    have hK : loopModK = 1000 := rfl
    have w2 := wt_list2_le (.list (ws'.map fun w => vsPairVal (w, vsWZ cs.length)))
      (.list ((vsUnitPairs cs.length cs).map vsPairVal))
    rw [eL, hK]
    simp only [List.length_map, vsUnitPairs, List.length_range] at w2 ⊢
    calc 1000 * (cs.length + 1) * _ ≤ 1000 * (N + 1) * (1000 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
            simp only [vsUnitPairs] at wup; omega)
      _ = 10 ^ 6 * (N + 1) ^ 4 := by ring
  have dapp := Det.call (Det.mk2 dm dup) ((append_spec happ _ _).mono fun w c hw =>
    ⟨hw.1, hw.2.trans (hw.1 ▸ kapp)⟩)
  rw [eL] at dapp
  have hfit := vsWFrRows_fits ⟨hp1, hpN, hdN, h', hc, hl⟩
  have hL : ∀ xt ∈ vsWFrPairs ws' cs,
      VsPairFits p N xt ∧ xt.1.length = d ∧ xt.2.length = cs.length := fun xt hxt => by
    obtain ⟨h1, h2, h3, h4⟩ := GI.Proved.vsWFrPairs_ok hp1 h' hc xt hxt
    exact ⟨⟨h1, h2, by omega, by omega⟩, h3, h4⟩
  have hLl : (vsWFrPairs ws' cs).length ≤ N := by simp [vsWFrPairs, vsUnitPairs]; omega
  have dins := Det.call (Det.mk3 a0 dapp (Det.mk2 Det.nil Det.nil))
    (vsInsertAll_spec hin (by omega) hpN hL hLl)
  have dget := Det.get' dins (Det.nat 0) (show [Val.list ((vsInsertAll p (vsWFrPairs ws' cs)).1.map
    VsRow.val), .list ((vsInsertAll p (vsWFrPairs ws' cs)).2.map natList)][0]? =
      some (.list ((vsWFrRows p ws' cs).map VsRow.val)) from rfl)
  refine FunDet.intro h0 (dget.mono ?_)
  have wacc := wt_vsAccVal_le hpN (by omega) hfit
  have wrows := wt_vsRows_le hfit.rows (hfit.nrows.trans (by omega))
  have wws' := wt_vsWVs_le (VsWFit.bnd h' hpN hdN) (show ws'.length ≤ N + 1 by omega)
  have wcs := wt_vsWVs_le (VsWFit.bnd hc hpN hdN) (show cs.length ≤ N + 1 by omega)
  have eU : (vsWVs ws').wt = (Val.list (ws'.map natList)).wt := rfl
  have eC : (vsWVs cs).wt = (Val.list (cs.map natList)).wt := rfl
  have wp := wt_nat_le p
  have wcl := wt_nat_le cs.length
  have w00 := wt_nat_le 0
  have wX := wt_list3_le (.nat p) (vsWVs ws') (vsWVs cs)
  have eX : X.wt = (Val.list [.nat p, vsWVs ws', vsWVs cs]).wt := rfl
  have w2a := wt_list2_le (natList (vsWZ cs.length)) (.list (ws'.map natList))
  have w2b := wt_list2_le (.nat cs.length) (.list (cs.map natList))
  have w2c := wt_list2_le (.list (ws'.map fun w => vsPairVal (w, vsWZ cs.length)))
    (.list ((vsUnitPairs cs.length cs).map vsPairVal))
  have w3 := wt_list3_le (.nat p) (.list ((vsWFrPairs ws' cs).map vsPairVal))
    (.list [.list [], .list []])
  have wn : (Val.list [Val.list [], Val.list []]).wt ≤ 20 := by decide
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := ws'.length) (B := 200 * (N + 1) ^ 2 + 100) (c := 1000)
    (k := 3) (W := (Val.list [natList (vsWZ cs.length), .list (ws'.map natList)]).wt +
      (Val.list (ws'.map fun w => vsPairVal (w, vsWZ cs.length))).wt) (by omega) (by omega)
      (by omega)
  have e5 : (N + 1) ^ (3 + 1) = (N + 1) ^ 4 := rfl
  rw [e5] at kmap
  have eAcc : (vsAccVal (vsInsertAll p (vsWFrPairs ws' cs))).wt =
    (Val.list [Val.list ((vsInsertAll p (vsWFrPairs ws' cs)).1.map VsRow.val),
      .list ((vsInsertAll p (vsWFrPairs ws' cs)).2.map natList)]).wt := rfl
  have eAcc0 : vsAccVal ([], []) = Val.list [.list [], .list []] := rfl
  have eR : vsWFrRows p ws' cs = (vsInsertAll p (vsWFrPairs ws' cs)).1 := rfl
  simp only [eAcc0, eR] at *
  omega

/-! ### The frame -/

/-- The frame, on `[p, d, ws', ws]`. -/
def vsWFrameF (comp rep frr : ℕ) : Expr :=
  .letE (.call comp (mk3 (arg 0) (arg 2) (arg 3)))
    (mk4 (mk4 (arg 0) (arg 1) (.call rep (mk2 (arg 1) (.nat 0)))
        (.call rep (mk2 (.length (.var 1)) (.nat 0))))
      (arg 2) (.var 1) (.call frr (mk3 (arg 0) (arg 2) (.var 1))))

/-- The frame program at base `b` (95 functions). -/
def vsWFrameFuns (b : ℕ) : List Expr :=
  [vsWFrameF (b + 1) (b + 46) (b + 49)] ++ vsWCompFuns (b + 1) ++ replicateFuns (b + 46) ++
    vsWFrRowsFuns (b + 49)

theorem vsWFrameFuns_length (b : ℕ) : (vsWFrameFuns b).length = 95 := rfl

theorem vsWComp_length_le {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {ws' ws : List (List ℕ)} (h' : GI.Proved.VsWFit p d ws') (hw : GI.Proved.VsWFit p d ws) :
    (vsWComp p ws' ws).length ≤ ws'.length + ws.length := by
  have := vsWRows_length_le hp hpN hdN (GI.Proved.vsWFit_append h' hw)
  simp only [vsWComp, List.length_map, List.length_drop, List.length_append] at this ⊢
  omega

theorem wt_vsWFrVal_le {p N d : ℕ} {ws' cs : List (List ℕ)} (H : VsWFrOK p N d ws' cs) :
    (vsWFrVal p d ws' cs).wt ≤ 500 * (N + 1) ^ 3 := by
  obtain ⟨hp1, hpN, hdN, h', hc, hl⟩ := H
  have hfit := vsWFrRows_fits ⟨hp1, hpN, hdN, h', hc, hl⟩
  have wrows := wt_vsRows_le hfit.rows (hfit.nrows.trans (by omega))
  have eR : vsWFrRows p ws' cs = (vsInsertAll p (vsWFrPairs ws' cs)).1 := rfl
  rw [← eR] at wrows
  have wws' := wt_vsWVs_le (VsWFit.bnd h' hpN hdN) (show ws'.length ≤ N + 1 by omega)
  have wcs := wt_vsWVs_le (VsWFit.bnd hc hpN hdN) (show cs.length ≤ N + 1 by omega)
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wz' : (natList (vsWZ cs.length)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have w4 := wt_list4_le (.nat p) (.nat d) (natList (vsWZ d)) (natList (vsWZ cs.length))
  have w4' := wt_list4_le (.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)])
    (vsWVs ws') (vsWVs cs) (.list ((vsWFrRows p ws' cs).map VsRow.val))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  show (Val.list [.list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)], vsWVs ws',
    vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)]).wt ≤ _
  omega

/-- **The frame program.** -/
theorem vsWFrame_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWFrameFuns b)) {p N d : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N) {ws' ws : List (List ℕ)}
    (h' : GI.Proved.VsWFit p d ws') (hw : GI.Proved.VsWFit p d ws)
    (hl : 2 * (ws'.length + ws.length) ≤ N) :
    FunDet P b (.list [.nat p, .nat d, vsWVs ws', vsWVs ws]) (vsWFrVal p d ws' (vsWComp p ws' ws))
      (2 * 10 ^ 8 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWFrameF (b + 1) (b + 46) (b + 49)) :=
    h.get (j := 0) (by simp [vsWFrameFuns])
  have hco : P.HasAt (b + 1) (vsWCompFuns (b + 1)) := h.block 1 rfl
  have hrep : P.HasAt (b + 46) (replicateFuns (b + 46)) := h.block 46 rfl
  have hfr : P.HasAt (b + 49) (vsWFrRowsFuns (b + 49)) := h.block 49 rfl
  set X := Val.list [.nat p, .nat d, vsWVs ws', vsWVs ws]
  set cs := vsWComp p ws' ws
  have hcf : GI.Proved.VsWFit p d cs := GI.Proved.vsWComp_fit (by omega) h' hw
  have hcl : cs.length ≤ ws'.length + ws.length := vsWComp_length_le (by omega) hpN hdN h' hw
  have H : VsWFrOK p N d ws' cs := ⟨hp1, hpN, hdN, h', hcf, by omega⟩
  have a k {v : Val} (hv : [Val.nat p, .nat d, vsWVs ws', vsWVs ws][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs ws', vsWVs ws]) (j := k) hv
  have dC := Det.call (Det.mk3 (a 0 rfl) (a 2 rfl) (a 3 rfl))
    (vsWComp_spec hco (by omega) hpN hdN h' hw (by omega))
  have b' k {v : Val} (hv : [Val.nat p, .nat d, vsWVs ws', vsWVs ws][k]? = some v) :=
    Det.arg' (P := P) (rest := [vsWVs cs]) (vs := [Val.nat p, .nat d, vsWVs ws', vsWVs ws]) (j := k) hv
  have v1 : Det P [X, vsWVs cs] (.var 1) (.list (cs.map natList)) _ := Det.var' rfl
  have dl := Det.length v1
  rw [List.length_map] at dl
  have dz1 := vsWZero_det hrep (b' 1 rfl) hdN
  have dz2 := vsWZero_det hrep dl (show cs.length ≤ N by omega)
  have dR := Det.call (Det.mk3 (b' 0 rfl) (b' 2 rfl) v1) (vsWFrRows_spec hfr H)
  have dbody := Det.mk4 (Det.mk4 (b' 0 rfl) (b' 1 rfl) dz1 dz2) (b' 2 rfl) v1 dR
  refine FunDet.intro h0 ((Det.letE dC dbody).mono ?_)
  have wF := wt_vsWFrVal_le H
  have wws' := wt_vsWVs_le (VsWFit.bnd h' hpN hdN) (show ws'.length ≤ N + 1 by omega)
  have wws := wt_vsWVs_le (VsWFit.bnd hw hpN hdN) (show ws.length ≤ N + 1 by omega)
  have wcs := wt_vsWVs_le (VsWFit.bnd hcf hpN hdN) (show cs.length ≤ N + 1 by omega)
  have eC : (vsWVs cs).wt = (Val.list (cs.map natList)).wt := rfl
  have eF : vsWFrVal p d ws' cs = .list [.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)] := rfl
  have wF2 := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list ((vsWFrRows p ws' cs).map VsRow.val)) (by simp)
  have wF1 := wt_le_wt_list (vs := [Val.list [.nat p, .nat d, natList (vsWZ d),
    natList (vsWZ cs.length)], vsWVs ws', vsWVs cs, .list ((vsWFrRows p ws' cs).map VsRow.val)])
    (v := .list [.nat p, .nat d, natList (vsWZ d), natList (vsWZ cs.length)]) (by simp)
  rw [← eF] at wF1 wF2
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have wX := wt_list4_le (.nat p) (.nat d) (vsWVs ws') (vsWVs ws)
  have eX : X.wt = (Val.list [.nat p, .nat d, vsWVs ws', vsWVs ws]).wt := rfl
  have w3 := wt_list3_le (.nat p) (vsWVs ws') (vsWVs ws)
  have w3' := wt_list3_le (.nat p) (vsWVs ws') (vsWVs cs)
  have hlc := length_lt_wt_list (cs.map natList)
  rw [List.length_map] at hlc
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have ez : (vsWVs (vsWComp p ws' ws)).wt = (Val.list (cs.map natList)).wt := rfl
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wz' : (natList (vsWZ cs.length)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wcl := wt_nat_le cs.length
  have w00 := wt_nat_le 0
  have e1 : (Val.list [Val.nat p, vsWVs ws', Val.list (List.map natList cs)]).wt =
    (Val.list [Val.nat p, vsWVs ws', vsWVs cs]).wt := rfl
  have e2 : (Val.list [Val.list [Val.nat p, Val.nat d, natList (vsWZ d), natList (vsWZ cs.length)],
      vsWVs ws', Val.list (List.map natList cs), Val.list (List.map VsRow.val (vsWFrRows p ws' cs))]).wt =
    (vsWFrVal p d ws' cs).wt := rfl
  omega

end GI.Impl
