module

public import Workspace.Impl.VsWProgMC

@[expose] public section

/-!
# The kernel and the fixed points of the Frobenius map as programs

Both programs flatten `M ^ p` (or `M ^ p - M`) for each `M ∈ Bm`, find the relations among
these vectors, and combine the `Bm` with each relation.

* `vsFNilFuns b` (116 functions), `vsFNil_spec`: on `[p, D, vsFMatsVal Bm]` the value
  `vsFMatsVal (vsFNilL p D Bm)`. Meaning: `GI.Proved.vsFNilL_span`.
* `vsFFixFuns b` (116 functions), `vsFFix_spec`: the same for `vsFFixL p D Bm`.
  Meaning: `GI.Proved.vsFFixL_span`.

Both need `D * D ≤ N` (the flattened matrices have length `D * D`).
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The flattened power, on `[[p, z], M]`. -/
def vsWPowFlatItemF (pow flat : ℕ) : Expr :=
  .call flat (.call pow (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1))))

/-- The flattened `M ^ p - M`, on `[[p, z], M]`. -/
def vsWFixFlatItemF (pow flat lin : ℕ) : Expr :=
  .call lin (.snoc (mk4 (.get (arg 0) (.nat 0)) (.nat 1) (.arith .sub (.get (arg 0) (.nat 0)) (.nat 1))
    (vsWPowFlatItemF pow flat)) (.call flat (arg 1)))

/-- The combination with one relation, on `[[p, D, Bm], a]`. -/
def vsWMCWrapF (mc : ℕ) : Expr :=
  .call mc (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (arg 1))

/-- The relations-and-combinations main function, on `[p, D, Bm]`. -/
def vsWRelF (fm ker mcm rep : ℕ) : Expr :=
  .call mcm (mk2 (mk3 (arg 0) (arg 1) (arg 2))
    (.call ker (mk2 (arg 0) (.call fm (mk2 (mk2 (arg 0) (.call rep (mk2 (arg 1) (.nat 0)))) (arg 2))))))

/-- The common layout (116 functions); `item` sits at `b + 4`. -/
def vsWRelFuns (item : Expr) (b : ℕ) : List Expr :=
  [vsWRelF (b + 1) (b + 5) (b + 41) (b + 76)] ++ mapFuns (b + 1) (b + 4) ++ [item] ++
    vsWKerFuns (b + 5) ++ mapFuns (b + 41) (b + 44) ++ [vsWMCWrapF (b + 45)] ++ vsWMCFuns (b + 45) ++
    replicateFuns (b + 76) ++ vsFMatPowFuns (b + 79) ++ vsWFlatFuns (b + 100) ++ vsLinFuns (b + 108)

theorem vsWRelFuns_length (item : Expr) (b : ℕ) : (vsWRelFuns item b).length = 116 := rfl

/-- The kernel program at base `b`. -/
def vsFNilFuns (b : ℕ) : List Expr := vsWRelFuns (vsWPowFlatItemF (b + 79) (b + 100)) b

/-- The fixed-point program at base `b`. -/
def vsFFixFuns (b : ℕ) : List Expr := vsWRelFuns (vsWFixFlatItemF (b + 79) (b + 100) (b + 108)) b

theorem vsWPowFlat_det {P : Program} {pow flat : ℕ}
    (hpw : P.HasAt pow (vsFMatPowFuns pow)) (hfl : P.HasAt flat (vsWFlatFuns flat)) {p N D : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hDD : D * D ≤ N) {M : List (List ℕ)} (hM : GI.Proved.VsWSq p D M) :
    Det P [.list [.list [.nat p, natList (vsWZ D)], vsWVs M]] (vsWPowFlatItemF pow flat)
      (natList (vsWPowFlat p D M)) (3 * 10 ^ 7 * (N + 1) ^ 6) := by
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  set C := Val.list [.nat p, natList (vsWZ D)]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [C, vsWVs M]) (j := 0) rfl
  have a1 : Det P [.list [C, vsWVs M]] (arg 1) (.list (M.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [C, vsWVs M]) (j := 1) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.nat p, natList (vsWZ D)][0]? = some (.nat p) from rfl)
  have g1 := Det.get' a0 (Det.nat 1)
    (show [Val.nat p, natList (vsWZ D)][1]? = some (natList (vsWZ D)) from rfl)
  have hz : ∀ y ∈ vsWZ D, y < p := fun y hy => by simp [vsWZ] at hy; omega
  have hzl : (vsWZ D).length = D := by simp [vsWZ]
  have hF := GI.Proved.vsWSq_vsFSq hM
  have dpw := Det.call (Det.mk3 g0 a1 g1) (vsFMatPow_spec hpw hp hpN hDN hF hz hzl)
  have hsq := vsFMatPowL_sq hp hF hz hzl (p - 1)
  have hsq' : GI.Proved.VsWSq p D (vsFMatPowL p M (vsWZ D) (p - 1)) := ⟨hsq.rows, hsq.len⟩
  have dfl := Det.call dpw (vsWFlat_spec hfl hpN hDD hsq')
  refine dfl.mono ?_
  have wM := wt_vsWVs_le (VsWFit.bnd hM.1 hpN hDN) (show M.length ≤ N + 1 by have := hM.2; omega)
  have eM : (vsWVs M).wt = (Val.list (M.map natList)).wt := rfl
  have wP := wt_vsWVs_le (VsWFit.bnd hsq'.1 hpN hDN) (show (vsFMatPowL p M (vsWZ D) (p - 1)).length ≤
    N + 1 by have := hsq'.2; omega)
  have eP : (vsWVs (vsFMatPowL p M (vsWZ D) (p - 1))).wt =
    (Val.list ((vsFMatPowL p M (vsWZ D) (p - 1)).map natList)).wt := rfl
  have wz : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wC := wt_list2_le (.nat p) (natList (vsWZ D))
  have w2 := wt_list2_le C (vsWVs M)
  have w3 := wt_list3_le (.nat p) (.list (M.map natList)) (natList (vsWZ D))
  have eCtx : vsFMatCtx p M (vsWZ D) = .list [.nat p, .list (M.map natList), natList (vsWZ D)] := rfl
  have w1 := wt_nat_le 1
  have w0 := wt_nat_le 0
  have eC : C.wt = (Val.list [.nat p, natList (vsWZ D)]).wt := rfl
  have hPF := GI.Proved.vsWPowFlat_fit (D := D) hp (Bm := [M]) (fun M' hM' => by
    rw [List.mem_singleton] at hM'; subst hM'; exact hM) (vsWPowFlat p D M) (by simp)
  have wo := wt_natList_le_sq (B := N) (xs := vsWPowFlat p D M)
    (fun y hy => (hPF.1 y hy).le.trans hpN) (by rw [hPF.2]; exact hDD)
  have ePF : natList (vsFMatPowL p M (vsWZ D) (p - 1)).flatten = natList (vsWPowFlat p D M) := rfl
  have wo' : (natList (vsFMatPowL p M (vsWZ D) (p - 1)).flatten).wt ≤ 5 * (N + 1) ^ 2 := wo
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem vsWPowFlatItem_spec {P : Program} {f pow flat : ℕ}
    (hf : P.funs[f]? = some (vsWPowFlatItemF pow flat)) (hpw : P.HasAt pow (vsFMatPowFuns pow))
    (hfl : P.HasAt flat (vsWFlatFuns flat)) {p N D : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    (hDD : D * D ≤ N) {M : List (List ℕ)} (hM : GI.Proved.VsWSq p D M) :
    FunDet P f (.list [.list [.nat p, natList (vsWZ D)], vsWVs M]) (natList (vsWPowFlat p D M))
      (3 * 10 ^ 7 * (N + 1) ^ 6) :=
  FunDet.intro hf (vsWPowFlat_det hpw hfl hp hpN hDD hM)

theorem vsWFixFlatItem_spec {P : Program} {f pow flat lin : ℕ}
    (hf : P.funs[f]? = some (vsWFixFlatItemF pow flat lin)) (hpw : P.HasAt pow (vsFMatPowFuns pow))
    (hfl : P.HasAt flat (vsWFlatFuns flat)) (hl : P.HasAt lin (vsLinFuns lin)) {p N D : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hDD : D * D ≤ N) {M : List (List ℕ)} (hM : GI.Proved.VsWSq p D M) :
    FunDet P f (.list [.list [.nat p, natList (vsWZ D)], vsWVs M]) (natList (vsWFixFlat p D M))
      (4 * 10 ^ 7 * (N + 1) ^ 6) := by
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  set C := Val.list [.nat p, natList (vsWZ D)]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [C, vsWVs M]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [C, vsWVs M]) (j := 1) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.nat p, natList (vsWZ D)][0]? = some (.nat p) from rfl)
  have hs : GI.Machine.BinOp.sub.eval p 1 = p - 1 := rfl
  have dsub := Det.arith' g0 (Det.nat 1) hs
  have dpf := vsWPowFlat_det hpw hfl hp hpN hDD hM
  have dfl := Det.call a1 (vsWFlat_spec hfl hpN hDD hM)
  have hPF := GI.Proved.vsWPowFlat_fit (D := D) hp (Bm := [M]) (fun M' hM' => by
    rw [List.mem_singleton] at hM'; subst hM'; exact hM) (vsWPowFlat p D M) (by simp)
  have hMf : ∀ y ∈ M.flatten, y ≤ N := by
    intro y hy
    obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
    exact ((hM.1 r hr).1 y hyr).le.trans hpN
  have hMl : M.flatten.length = D * D := by
    rw [List.length_flatten]
    have : ∀ r ∈ M, r.length = D := fun r hr => (hM.1 r hr).2
    rw [List.map_congr_left this, List.map_const', List.sum_replicate, hM.2, smul_eq_mul]
  have dlin := Det.call (Det.snoc (Det.mk4 g0 (Det.nat 1) dsub dpf) dfl)
    (vsLin_spec hl (p := p) (a := 1) (b := p - 1) (N := N) hp
      (fun y hy => (hPF.1 y hy).le.trans hpN) hMf (by rw [hPF.2]; exact hDD) (by rw [hMl]; exact hDD)
      (by rw [hPF.2, hMl]) hpN (by omega) (by omega))
  refine FunDet.intro hf (dlin.mono ?_)
  have wM := wt_vsWVs_le (VsWFit.bnd hM.1 hpN hDN) (show M.length ≤ N + 1 by have := hM.2; omega)
  have wz : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wo := wt_natList_le_sq (B := N) (xs := vsWPowFlat p D M)
    (fun y hy => (hPF.1 y hy).le.trans hpN) (by rw [hPF.2]; exact hDD)
  have wF := wt_natList_le_sq (B := N) (xs := M.flatten) hMf (by rw [hMl]; exact hDD)
  have wp := wt_nat_le p
  have wp1 := wt_nat_le (p - 1)
  have w1 := wt_nat_le 1
  have w0 := wt_nat_le 0
  have wC := wt_list2_le (.nat p) (natList (vsWZ D))
  have w2 := wt_list2_le C (vsWVs M)
  have w4 := wt_list4_le (.nat p) (.nat 1) (.nat (p - 1)) (natList (vsWPowFlat p D M))
  have wA := wt_vsLinArg_le (p := p) (a := 1) (b := p - 1) (fun y hy => (hPF.1 y hy).le.trans hpN) hMf
    (by rw [hPF.2]; exact hDD) (by rw [hMl]; exact hDD) hpN (by omega) (by omega)
  have eA : (Val.list ([Val.nat p, Val.nat 1, Val.nat (p - 1), natList (vsWPowFlat p D M)] ++
    [natList M.flatten])).wt = (vsLinArg p 1 (p - 1) (vsWPowFlat p D M) M.flatten).wt := rfl
  have wL := wt_natList_le_sq (B := N) (xs := vsLin p 1 (p - 1) (vsWPowFlat p D M) M.flatten)
    (fun y hy => (vsLin_lt hp _ _ y hy).le.trans hpN) (by rw [vsLin_length, hPF.2]; exact hDD)
  have eL : vsWFixFlat p D M = vsLin p 1 (p - 1) (vsWPowFlat p D M) M.flatten := rfl
  have eC : C.wt = (Val.list [.nat p, natList (vsWZ D)]).wt := rfl
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem vsWMCWrap_spec {P : Program} {f mc : ℕ} (hf : P.funs[f]? = some (vsWMCWrapF mc))
    (h : P.HasAt mc (vsWMCFuns mc)) {p N D : ℕ} (hp : 0 < p)
    (hpN : p ≤ N) (hDN : D ≤ N) {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M)
    (hBl : Bm.length ≤ N) {a : List ℕ} (ha : ∀ y ∈ a, y < p) (hal : a.length ≤ N)
    (hBa : Bm.length ≤ a.length) :
    FunDet P f (.list [.list [.nat p, .nat D, vsFMatsVal Bm], natList a]) (vsWVs (vsWMC p D Bm a))
      (2 * 10 ^ 10 * (N + 1) ^ 6) := by
  have a0 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D, vsFMatsVal Bm], natList a]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := [])
    (vs := [.list [.nat p, .nat D, vsFMatsVal Bm], natList a]) (j := 1) rfl
  have g k {v : Val} (hv : [Val.nat p, .nat D, vsFMatsVal Bm][k]? = some v) := Det.get' a0 (Det.nat k) hv
  refine FunDet.intro hf ((Det.call (Det.mk4 (g 0 rfl) (g 1 rfl) (g 2 rfl) a1)
    (vsWMC_spec h hp hpN hDN hB hBl ha hal hBa)).mono ?_)
  have wB := wt_vsWMats_le hpN hDN hB (by omega)
  have wa := wt_natList_le_sq (B := N) (xs := a) (fun y hy => (ha y hy).le.trans hpN) hal
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2' := wt_nat_le 2
  have wC := wt_list3_le (.nat p) (.nat D) (vsFMatsVal Bm)
  have w2 := wt_list2_le (.list [.nat p, .nat D, vsFMatsVal Bm]) (natList a)
  have hMC := GI.Proved.vsWMC_sq (p := p) (D := D) hp Bm a
  have wO := wt_vsWVs_le (VsWFit.bnd hMC.1 hpN hDN) (show (vsWMC p D Bm a).length ≤ N + 1 by
    rw [hMC.2]; omega)
  have w4 := wt_list4_le (.nat p) (.nat D) (vsFMatsVal Bm) (natList a)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2' : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- The common part of `vsFNil_spec` and `vsFFix_spec`: the item at `b + 4` sends `M` to `g M`. -/
theorem vsWRel_spec {P : Program} {item : Expr} {b : ℕ} (h : P.HasAt b (vsWRelFuns item b))
    {p N D : ℕ} (hp : 1 < p) (hpN : p ≤ N) (hDD : D * D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M) (hBl : Bm.length ≤ N) (g : List (List ℕ) → List ℕ)
    (hg : GI.Proved.VsWFit p (D * D) (Bm.map g))
    (hit : ∀ M ∈ Bm, FunDet P (b + 4) (.list [.list [.nat p, natList (vsWZ D)], vsWVs M])
      (natList (g M)) (4 * 10 ^ 7 * (N + 1) ^ 6)) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Bm])
      (vsFMatsVal ((vsWKer p (Bm.map g)).map (vsWMC p D Bm))) (10 ^ 14 * (N + 1) ^ 7) := by
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  have h0 : P.funs[b]? = some (vsWRelF (b + 1) (b + 5) (b + 41) (b + 76)) :=
    h.get (j := 0) (by rw [vsWRelFuns_length]; omega)
  have hm1 : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hker : P.HasAt (b + 5) (vsWKerFuns (b + 5)) := h.block 5 rfl
  have hm2 : P.HasAt (b + 41) (mapFuns (b + 41) (b + 44)) := h.block 41 rfl
  have hw : P.funs[b + 44 + 0]? = some (vsWMCWrapF (b + 45)) :=
    (h.block 44 (gs := [vsWMCWrapF (b + 45)]) rfl).get (j := 0) (by simp)
  have hmc : P.HasAt (b + 45) (vsWMCFuns (b + 45)) := h.block 45 rfl
  have hrep : P.HasAt (b + 76) (replicateFuns (b + 76)) := h.block 76 rfl
  have ar k {v : Val} (hv : [Val.nat p, .nat D, vsFMatsVal Bm][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat D, vsFMatsVal Bm]) (j := k) hv
  have a2 : Det P [.list [.nat p, .nat D, vsFMatsVal Bm]] (arg 2) (.list (Bm.map vsWVs)) _ := ar 2 rfl
  have dz := vsWZero_det hrep (ar 1 rfl) hDN
  have dm1 := Det.call (Det.mk2 (Det.mk2 (ar 0 rfl) dz) a2)
    (vsQ_map hm1 Bm vsWVs (fun M => natList (g M)) vsWVs_injective
      (c := .list [.nat p, natList (vsWZ D)]) hit)
  have e1 : Val.list (Bm.map fun M => natList (g M)) = vsWVs (Bm.map g) := by
    simp [vsWVs, List.map_map, Function.comp_def]
  rw [e1] at dm1
  have hgl : (Bm.map g).length ≤ N := by simpa using hBl
  have dk := Det.call (Det.mk2 (ar 0 rfl) dm1) (vsWKer_spec hker hp hpN hDD hg hgl)
  have hK := GI.Proved.vsWKer_fit hp hg
  have hKl := vsWKer_length_le hp hpN hDD hg hgl
  have hBl' : (Bm.map g).length = Bm.length := List.length_map _
  have dm2 := Det.call (Det.mk2 (Det.mk3 (ar 0 rfl) (ar 1 rfl) (ar 2 rfl)) dk)
    (vsQ_map hm2 (vsWKer p (Bm.map g)) natList (fun a => vsWVs (vsWMC p D Bm a)) vsQ_natList_injective
      (c := .list [.nat p, .nat D, vsFMatsVal Bm]) fun a ha =>
        vsWMCWrap_spec hw hmc (by omega) hpN hDN hB hBl (hK a ha).1 (by rw [(hK a ha).2]; omega)
          (by rw [(hK a ha).2, hBl']))
  have e2 : Val.list ((vsWKer p (Bm.map g)).map fun a => vsWVs (vsWMC p D Bm a)) =
      vsFMatsVal ((vsWKer p (Bm.map g)).map (vsWMC p D Bm)) := by
    simp [vsWVs, vsFMatsVal, List.map_map, Function.comp_def]
  rw [e2] at dm2
  refine FunDet.intro h0 (dm2.mono ?_)
  have wB := wt_vsWMats_le hpN hDN hB (by omega)
  have eB : (vsFMatsVal Bm).wt = (Val.list (Bm.map vsWVs)).wt := rfl
  have wO := wt_vsWMats_le (Bm := (vsWKer p (Bm.map g)).map (vsWMC p D Bm)) hpN hDN
    (fun M hM => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hM
      exact GI.Proved.vsWMC_sq (by omega) Bm a) (by simp; omega)
  have wG := wt_vsWVs_le (VsWFit.bnd hg hpN hDD) (by omega)
  have wK := wt_vsWVs_le (VsWFit.bnd hK hpN (by omega)) (by omega)
  have eK : (vsWVs (vsWKer p (Bm.map g))).wt = (Val.list ((vsWKer p (Bm.map g)).map natList)).wt := rfl
  have wz : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have wA := wt_list3_le (.nat p) (.nat D) (vsFMatsVal Bm)
  have eg : (Val.list [.list [.nat p, .nat D, vsFMatsVal Bm], vsWVs (vsWKer p (Bm.map g))]).wt =
    (Val.list [.list [.nat p, .nat D, vsFMatsVal Bm], .list ((vsWKer p (Bm.map g)).map natList)]).wt := rfl
  have wc := wt_list2_le (.nat p) (natList (vsWZ D))
  have w1 := wt_list2_le (.list [.nat p, natList (vsWZ D)]) (.list (Bm.map vsWVs))
  have w2 := wt_list2_le (.nat p) (vsWVs (Bm.map g))
  have w3 := wt_list2_le (.list [.nat p, .nat D, vsFMatsVal Bm])
    (.list ((vsWKer p (Bm.map g)).map natList))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q7 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have k1 := vsW_mapCost (N := N) (n := Bm.length) (B := 4 * 10 ^ 7 * (N + 1) ^ 6)
    (c := 4 * 10 ^ 7) (k := 6)
    (W := (Val.list [.list [.nat p, natList (vsWZ D)], .list (Bm.map vsWVs)]).wt +
      (Val.list (Bm.map fun M => natList (g M))).wt) hBl le_rfl (by rw [e1]; omega)
  have k2 := vsW_mapCost (N := N) (n := (vsWKer p (Bm.map g)).length) (B := 2 * 10 ^ 10 * (N + 1) ^ 6)
    (c := 2 * 10 ^ 10) (k := 6)
    (W := (Val.list [.list [.nat p, .nat D, vsFMatsVal Bm],
      .list ((vsWKer p (Bm.map g)).map natList)]).wt +
      (Val.list ((vsWKer p (Bm.map g)).map fun a => vsWVs (vsWMC p D Bm a))).wt)
    (by omega) le_rfl (by rw [e2]; omega)
  have e7 : (N + 1) ^ (6 + 1) = (N + 1) ^ 7 := rfl
  rw [e1] at k1
  rw [e2] at k2
  omega

/-- **The Frobenius kernel program.** -/
theorem vsFNil_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFNilFuns b)) {p N D : ℕ} (hp : 1 < p)
    (hpN : p ≤ N) (hDD : D * D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M) (hBl : Bm.length ≤ N) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Bm]) (vsFMatsVal (vsFNilL p D Bm))
      (10 ^ 14 * (N + 1) ^ 7) := by
  have hit : P.funs[b + 4]? = some (vsWPowFlatItemF (b + 79) (b + 100)) :=
    h.get (j := 4) (by rw [vsFNilFuns, vsWRelFuns_length]; omega)
  have hpw : P.HasAt (b + 79) (vsFMatPowFuns (b + 79)) := h.block 79 rfl
  have hfl : P.HasAt (b + 100) (vsWFlatFuns (b + 100)) := h.block 100 rfl
  exact vsWRel_spec h hp hpN hDD hB hBl (vsWPowFlat p D) (GI.Proved.vsWPowFlat_fit (by omega) hB)
    fun M hM => (vsWPowFlatItem_spec hit hpw hfl (by omega) hpN hDD (hB M hM)).mono (by omega)

/-- **The Frobenius fixed-point program.** -/
theorem vsFFix_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsFFixFuns b)) {p N D : ℕ} (hp : 1 < p)
    (hpN : p ≤ N) (hDD : D * D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M) (hBl : Bm.length ≤ N) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Bm]) (vsFMatsVal (vsFFixL p D Bm))
      (10 ^ 14 * (N + 1) ^ 7) := by
  have hit : P.funs[b + 4]? = some (vsWFixFlatItemF (b + 79) (b + 100) (b + 108)) :=
    h.get (j := 4) (by rw [vsFFixFuns, vsWRelFuns_length]; omega)
  have hpw : P.HasAt (b + 79) (vsFMatPowFuns (b + 79)) := h.block 79 rfl
  have hfl : P.HasAt (b + 100) (vsWFlatFuns (b + 100)) := h.block 100 rfl
  have hl : P.HasAt (b + 108) (vsLinFuns (b + 108)) := h.block 108 rfl
  exact vsWRel_spec h hp hpN hDD hB hBl (vsWFixFlat p D) (GI.Proved.vsWFixFlat_fit (by omega) hB)
    fun M hM => vsWFixFlatItem_spec hit hpw hfl hl (by omega) hpN hDD (hB M hM)

end GI.Impl
