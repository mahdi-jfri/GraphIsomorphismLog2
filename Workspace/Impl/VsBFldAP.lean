module

public import Workspace.Impl.VsBWalk
public import Workspace.Impl.VsBAct
public import Workspace.Impl.VsQAnaBase
public import Workspace.Proved.VsBFldA

@[expose] public section

/-!
# The programs of the λ-chain

The λ-chain needs three small programs, all on local matrices carried as `vsQE p D 0 M`:
* the action of stage `p` on local vectors, `y ↦ Λ(g)^{F_{p+2}} y` (`vsBActA_spec`);
* the point of a target unit `u`, `u^{F_{p+2}} e₀` (`vsBTkA_spec`);
* the update `u ↦ Λ(t)⁻¹ u` (`vsBUpA_spec`).

The context is `vsBCtxA s = [Γ, frame, p, 0^D, n, e₀]`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The context of the λ-chain programs. -/
noncomputable def vsBCtxA (s : VsQSt I) (hD : 1 ≤ vsQD s) : Val :=
  .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p, natList (List.replicate (vsQD s) 0),
    .nat I.n, natList (vsQVec (vsBe0 s hD))]

/-- On `[ctx, g]`: the carried local matrix of `g`. -/
def vsBLcarE (item : ℕ) : Expr :=
  mk4 (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3)) (.nat 0)
    (.call item (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1)))

/-- On `[ctx, q, X, v]`: the list `0 :: X^{F_q} v`. -/
def vsBWaE (walk row appd : ℕ) : Expr :=
  .letE (.call walk (mk3 (arg 1) (arg 2) (.get (arg 0) (.nat 4))))
    (.call appd (mk2 (mk1 (.nat 0)) (.call row (mk2 (mk3 (.get (arg 0) (.nat 2))
      (.get (.var 1) (.nat 3)) (.get (arg 0) (.nat 3))) (arg 3)))))

/-- The action, on `[[ctx, p], g, 0 :: y]`. -/
def vsBActAE (wa lcar tail : ℕ) : Expr :=
  .call wa (mk4 (.get (arg 0) (.nat 0)) (.arith .add (.get (arg 0) (.nat 1)) (.nat 2))
    (.call lcar (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.call tail (arg 2)))

/-- The point of a target, on `[ctx, p, u]`. -/
def vsBTkAE (wa : ℕ) : Expr :=
  .call wa (mk4 (arg 0) (.arith .add (arg 1) (.nat 2)) (arg 2) (.get (arg 0) (.nat 5)))

/-- The update, on `[ctx, u, t]`. -/
def vsBUpAE (mul lcar inv : ℕ) : Expr :=
  .call mul (mk2 (.call lcar (mk2 (arg 0) (.call inv (arg 2)))) (arg 1))

/-- The λ-chain programs at base `b` (80 functions): the action at `b + 1`, the point at `b + 2`,
the update at `b + 3`; `phi` is outside. -/
def vsBAFuns (b phi : ℕ) : List Expr :=
  [vsBWaE (b + 39) (b + 49) (b + 65), vsBActAE b (b + 4) (b + 62), vsBTkAE b,
    vsBUpAE (b + 42) (b + 4) (b + 68), vsBLcarE (b + 5), vsQLCItemE phi (b + 6)] ++
  (vsWLocFuns (b + 6) ++ (vsBWalkFuns (b + 39) (b + 42 + 3) ++ (vsQGLFuns (b + 42) ++
    (linTailFuns (b + 62) ++ (appendFuns (b + 65) ++ invFuns (b + 68))))))

theorem vsBAFuns_length (b phi : ℕ) : (vsBAFuns b phi).length = 80 := by
  simp [vsBAFuns, vsWLocFuns_length, vsBWalkFuns, vsQGLFuns_length, loopFuns, linTailFuns,
    appendFuns, invFuns, mapFuns, rangeFuns, findFuns]

/-- The stored local matrix of `g` is the canonical list of `Λ(g)ᵀ`. -/
theorem vsB_loc_eq (s : VsQSt I) (g : Perm (Fin I.n)) :
    vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ) = vsQL (vsQLam s g)ᵀ := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hsq := vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ)
  rw [vsQLam, vsWM, transpose_transpose]
  exact vsQL_of_sq ⟨hsq.2, hsq.1⟩

set_option maxHeartbeats 2000000 in
/-- The local matrix of one element (the item function of `vsQLC_spec`). -/
theorem vsB_item_spec {P : Program} {f phi loc Cφ S Tm : ℕ}
    (h1 : P.funs[f]? = some (vsQLCItemE phi loc)) (hloc : P.HasAt loc (vsWLocFuns loc))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    FunDet P f (.list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], encPerm g])
      (vsWVs (vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ))) (Cφ + 10 ^ 14 * S ^ 5) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hSn := hS.n
  have hSd := hS.d
  have hSp := hS.p
  have hp1 := I.prime.one_lt
  set N := 4 * S with hN
  have hcl : (vsQCs s).length ≤ s.ws'.length + s.ws.length :=
    vsWComp_length_le I.prime.pos (show I.p ≤ N by omega) (show I.d ≤ N by omega) hs.fit' hs.fit
  have hwl := hs.wl
  have hwl' := hs.wl'
  have hFr : VsWFrOK I.p N I.d s.ws' (vsQCs s) :=
    ⟨hp1, by omega, by omega, hs.fit', vsWComp_fit I.prime.pos hs.fit' hs.fit, by omega⟩
  have hsz : VsQSz I.p I.d (vsQExp I) S := by
    refine ⟨by omega, by omega, ?_, I.prime.pos⟩
    have h1 := hS.g
    have h2 : (Val.nat (vsQExp I)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
      wt_le_wt_list (show Val.nat (vsQExp I) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
        .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
        by simp)
    have h3 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt :=
      wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
        vsQE I.p I.d (vsQExp I) 1] by simp)
    omega
  have p5 := vsQ_four_pow 5 hS1
  have p3 := vsQ_four_pow 3 hS1
  have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
  have q13 : S ≤ S ^ 3 := by have := hS.pow_le (show 1 ≤ 3 by omega); simpa using this
  have q23 : S ^ 2 ≤ S ^ 3 := hS.pow_le (by omega)
  have q02 : 1 ≤ S ^ 2 := by have := hS.pow_le (show 0 ≤ 2 by omega); simpa using this
  norm_num at p5 p3
  set Γ := vsQGam I with hΓ
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s) with hfrV
  have wfr : frV.wt ≤ 500 * (N + 1) ^ 3 := wt_vsWFrVal_le hFr
  have hgG : g ∈ gens I.gs := hs.prob.le hg
  set c := Val.list [Γ, frV]
  set a := Val.list [c, encPerm g]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 1) rfl
  have gΓ := Det.get' a0 (Det.nat 0) (show [Γ, frV][0]? = some Γ from rfl)
  have gF := Det.get' a0 (Det.nat 1) (show [Γ, frV][1]? = some frV from rfl)
  have dE := Det.call (Det.mk2 gΓ a1) (hphi g hgG)
  have hsq := vsQL_sq (vsQPhi I g)ᵀ
  have dA := Det.get' dE (Det.nat 3) (show [Val.nat I.p, natList (List.replicate I.d 0),
    .nat (vsQExp I), .list ((vsQL (vsQPhi I g)ᵀ).map natList)][3]? =
      some (vsWVs (vsQL (vsQPhi I g)ᵀ)) from rfl)
  have dL := Det.call (Det.mk2 gF dA) (vsWLoc_spec hloc hFr (A := vsQL (vsQPhi I g)ᵀ)
    ⟨fun r hr => hsq.rows r hr, hsq.len⟩)
  refine FunDet.intro h1 (dL.mono ?_)
  have wE := wt_vsQE_le hsz (vsQPhi I g)
  have wA := wt_vsQL_le hsz (vsQPhi I g)ᵀ
  have wg := hS.wt_perm g
  have wΓ := hS.g
  have wc := wt_list2_le Γ frV
  have wa := wt_list2_le c (encPerm g)
  have w2 := wt_list2_le Γ (encPerm g)
  have w3 := wt_list2_le frV (vsWVs (vsQL (vsQPhi I g)ᵀ))
  have wL := wt_vsWVs_le (N := N) (VsWFit.bnd (vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s)
    (vsQL (vsQPhi I g)ᵀ)).1 (by omega) (by omega))
    (by rw [(vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ)).2]; omega)
  have eA : (vsWVs (vsQL (vsQPhi I g)ᵀ)).wt = (Val.list ((vsQL (vsQPhi I g)ᵀ).map natList)).wt :=
    rfl
  have ec : c.wt = (Val.list [Γ, frV]).wt := rfl
  have ea : a.wt = (Val.list [c, encPerm g]).wt := rfl
  have := wt_nat_le 3
  have eΓ : Γ.wt = (vsQGam I).wt := rfl
  have eN5 : (N + 1) ^ 5 = (4 * S + 1) ^ 5 := rfl
  have q1 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    nlinarith
  rw [hN] at wfr wL
  omega

theorem vsB_row_eq [NeZero I.p] {D : ℕ} (W : Matrix (Fin D) (Fin D) (ZMod I.p)) (y : Fin D → ZMod I.p) :
    vsFRowMul I.p (vsQVec y) (vsQL Wᵀ) (vsWZ D) = vsQVec (W *ᵥ y) := by
  have hsq := vsQL_sq (p := I.p) Wᵀ
  have hfit := vsFRowMul_fit (d := D) I.prime.pos (vsQVec y) (vsQL Wᵀ) _ (List.mem_singleton_self _)
  rw [vsQVec_of hfit.2 hfit.1]
  show vsQVec (vsWV I.p D _) = _
  rw [vsWV_img hsq.len (fun r hr => (hsq.rows r hr).2.le), vsWV_vsQVec]
  congr 1
  rw [vsWLin, Matrix.toLin'_apply, vsWM, vsFMatrix_vsQL, transpose_transpose]

section Specs

variable {P : Program} {b phi Cφ S Tm : ℕ} (h : P.HasAt b (vsBAFuns b phi))
  (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
    (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
  (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s)
include h hS hs

omit h in
theorem vsB_szA : VsQSz I.p (vsQD s) 0 (4 * S) :=
  ⟨by have := hS.p; omega, by have := vsQD_le hs; have := hS.d; omega,
    by have := hS.one_le; have : (Val.nat 0).wt = 2 := rfl; omega, I.prime.pos⟩

omit h in
theorem vsB_wt_ctxA : (vsBCtxA s hD).wt ≤ 10 ^ 6 * S ^ 3 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have wfr := vsQ_wt_fr hS hs
  have wΓ := hS.g
  have hDd := vsQD_le hs
  have wz := wt_natList_le_sq (B := S) (xs := List.replicate (vsQD s) 0)
    (fun y hy => by rw [List.eq_of_mem_replicate hy]; omega) (by simp; have := hS.d; omega)
  have we := wt_natList_le_sq (B := S) (xs := vsQVec (vsBe0 s hD))
    (fun y hy => (vsQVec_lt _ y hy).le.trans hS.p) (by rw [vsQVec_length]; have := hS.d; omega)
  have := wt_list_le [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have := wt_nat_le I.p; have := wt_nat_le I.n; have := hS.p; have := hS.n
  have hS1 := hS.one_le
  have q2 : (S + 1) ^ 2 ≤ 4 * S ^ 3 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have q13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  show (Val.list _).wt ≤ _
  omega

omit h in
theorem vsB_wt_carA (X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    (vsQE I.p (vsQD s) 0 X).wt ≤ 2 * 10 ^ 4 * S ^ 3 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have := wt_vsQE_le (vsB_szA hS hs) X
  have := vsQ_four_pow 3 hS.one_le
  norm_num at this
  omega

include hphi in
set_option maxHeartbeats 2000000 in
/-- The carried local matrix of an element. -/
theorem vsB_lcar_spec {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    FunDet P (b + 4) (.list [vsBCtxA s hD, encPerm g]) (vsQE I.p (vsQD s) 0 (vsQLam s g))
      (Cφ + 10 ^ 15 * S ^ 5) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h4 : P.funs[b + 4]? = some (vsBLcarE (b + 5)) := h.get (j := 4) (by rw [vsBAFuns_length]; omega)
  have h5 : P.funs[b + 5]? = some (vsQLCItemE phi (b + 6)) :=
    h.get (j := 5) (by rw [vsBAFuns_length]; omega)
  have hloc : P.HasAt (b + 6) (vsWLocFuns (b + 6)) := h.block 6 rfl
  set c := vsBCtxA s hD
  have a0 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 1) rfl
  have lc : ∀ k v, [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][k]? = some v →
      Det P [.list [c, encPerm g]] (.get (arg 0) (.nat k)) v _ :=
    fun k v hv => Det.get' a0 (Det.nat k) hv
  have ditem := Det.call (Det.mk2 (Det.mk2 (lc 0 _ rfl) (lc 1 _ rfl)) a1)
    (vsB_item_spec h5 hloc hphi hS hs hg)
  rw [vsB_loc_eq] at ditem
  have dall := Det.mk4 (lc 2 _ rfl) (lc 3 _ rfl) (Det.nat 0) ditem
  refine FunDet.intro h4 (dall.mono ?_)
  have wc := vsB_wt_ctxA hS hs hD
  have wE := vsB_wt_carA hS hs (vsQLam s g)
  have wL : (vsWVs (vsQL (vsQLam s g)ᵀ)).wt < (vsQE I.p (vsQD s) 0 (vsQLam s g)).wt :=
    wt_le_wt_list (by simp [vsQE, vsWVs])
  have wg := hS.wt_perm g
  have wa := wt_list2_le c (encPerm g)
  have w2 := wt_list2_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]) (encPerm g)
  have w22 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
  have wfr := vsQ_wt_fr hS hs
  have wΓ := hS.g
  have wΓc : (vsQGam I).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxA])
  have wfc : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxA])
  have wpc : (Val.nat I.p).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxA])
  have wzc : (natList (List.replicate (vsQD s) 0)).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxA])
  have w4 := wt_list4_le (.nat I.p) (natList (List.replicate (vsQD s) 0)) (.nat 0)
    (vsWVs (vsQL (vsQLam s g)ᵀ))
  have e4 : (Val.list [.nat I.p, natList (List.replicate (vsQD s) 0), .nat 0,
    vsWVs (vsQL (vsQLam s g)ᵀ)]).wt = (vsQE I.p (vsQD s) 0 (vsQLam s g)).wt := rfl
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
  have hS1 := hS.one_le
  have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
  have q13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have q23 : S ^ 2 ≤ S ^ 3 := hS.pow_le (by omega)
  have ec : c.wt = (vsBCtxA s hD).wt := rfl
  omega

omit h in
theorem vsB_wt_vecA (y : Fin (vsQD s) → ZMod I.p) : (natList (vsQVec y)).wt ≤ 20 * S ^ 2 ∧
    (natList (0 :: vsQVec y)).wt ≤ 20 * S ^ 2 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hDd := vsQD_le hs
  have hS1 := hS.one_le
  have q : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have w1 := wt_natList_le_sq (B := S) (xs := vsQVec y)
    (fun z hz => (vsQVec_lt _ z hz).le.trans hS.p) (by rw [vsQVec_length]; have := hS.d; omega)
  have w2 := wt_natList_le_sq (B := S) (xs := 0 :: vsQVec y)
    (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact (vsQVec_lt _ z hz).le.trans hS.p) (by simp [vsQVec_length]; have := hS.d; omega)
  omega

set_option maxHeartbeats 4000000 in
/-- The walk followed by applying the result to a vector. -/
theorem vsB_wa_spec {q : ℕ} (hq : q ≤ 4 * S) (X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))
    (y : Fin (vsQD s) → ZMod I.p) :
    FunDet P b (.list [vsBCtxA s hD, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)])
      (natList (0 :: vsQVec ((X ^ vsBF I.n q) *ᵥ y))) (10 ^ 17 * S ^ 7) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hz := vsB_szA hS hs
  have h0 : P.funs[b]? = some (vsBWaE (b + 39) (b + 49) (b + 65)) :=
    h.get (j := 0) (by rw [vsBAFuns_length]; omega)
  have hw : P.HasAt (b + 39) (vsBWalkFuns (b + 39) (b + 42 + 3)) := h.block 39 rfl
  have hg : P.HasAt (b + 42) (vsQGLFuns (b + 42)) := h.block 42 rfl
  have hap : P.HasAt (b + 65) (appendFuns (b + 65)) := h.block 65 rfl
  have hmm : P.HasAt (b + 46) (vsFMatMulFuns (b + 46)) := hg.block 4 rfl
  have hrow : P.funs[b + 49]? = some (vsFRowF (b + 50)) :=
    hmm.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)
  have hfo : P.HasAt (b + 50) (foldlFuns (b + 50) (b + 53)) := hmm.block 4 rfl
  have hst : P.funs[b + 53]? = some (vsFMulStepF (b + 54)) :=
    hmm.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)
  have hl : P.HasAt (b + 54) (vsLinFuns (b + 54)) := hmm.block 8 rfl
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hpS := hS.p
  have hdS := hS.d
  have hnS := hS.n
  set c := vsBCtxA s hD
  set W := vsBWalk I.n q X
  set a := Val.list [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)])
    (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)])
    (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)])
    (j := 2) rfl
  have dn := Det.get' g0 (Det.nat 4) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][4]? = some (.nat I.n) from rfl)
  have dW := Det.call (Det.mk3 g1 g2 dn)
    (vsBWalk_spec hw hg hz q I.n (by omega) hq X)
  -- in the environment `[a, W]`
  have g0' := Det.arg' (P := P) (rest := [vsQE I.p (vsQD s) 0 W])
    (vs := [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)]) (j := 0) rfl
  have g3' := Det.arg' (P := P) (rest := [vsQE I.p (vsQD s) 0 W])
    (vs := [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)]) (j := 3) rfl
  have dp := Det.get' g0' (Det.nat 2) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][2]? = some (.nat I.p) from rfl)
  have dz := Det.get' g0' (Det.nat 3) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][3]? =
        some (natList (List.replicate (vsQD s) 0)) from rfl)
  have dB := Det.get' (Det.var' (P := P) (env := [a, vsQE I.p (vsQD s) 0 W]) (i := 1) rfl) (Det.nat 3)
    (show [Val.nat I.p, natList (List.replicate (vsQD s) 0), .nat 0, .list ((vsQL Wᵀ).map natList)][3]? =
      some (.list ((vsQL Wᵀ).map natList)) from rfl)
  have hsq := vsQL_sq (p := I.p) Wᵀ
  have hRF : VsFRowFits I.p (4 * S) (vsQVec y) (vsQL Wᵀ) (vsWZ (vsQD s)) :=
    { ha := vsQVec_lt y
      la := by rw [vsQVec_length]; omega
      hz := fun z hz => by simp only [vsWZ] at hz; rw [List.eq_of_mem_replicate hz]; exact I.prime.pos
      lz := by simp [vsWZ]; omega
      hB := fun r hr z hz => ((hsq.rows r hr).1 z hz).le.trans (by omega)
      lB := fun r hr => by rw [(hsq.rows r hr).2]; omega
      zB := fun r hr => by rw [(hsq.rows r hr).2]; simp [vsWZ]
      Ba := by rw [hsq.len, vsQVec_length] }
  have drow := Det.call (Det.mk2 (Det.mk3 dp dB dz) g3')
    (vsFRow_spec hrow hfo hst hl I.prime.pos (by omega) hRF)
  have erow := vsB_row_eq W y
  simp only [vsWZ] at erow
  rw [erow] at drow
  have kap : loopModK * ((vsQVec (W *ᵥ y)).map Val.nat).length.succ *
      ((Val.list [.list [.nat 0], .list ((vsQVec (W *ᵥ y)).map Val.nat)]).wt +
        ((vsQVec (W *ᵥ y)).map Val.nat).length +
        (Val.list ([Val.nat 0] ++ (vsQVec (W *ᵥ y)).map Val.nat)).wt + 1) ≤ 10 ^ 6 * S ^ 3 := by
    have w2 := wt_list2_le (.list [.nat 0]) (.list ((vsQVec (W *ᵥ y)).map Val.nat))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have wv := vsB_wt_vecA hS hs (W *ᵥ y)
    have e1 : (Val.list ((vsQVec (W *ᵥ y)).map Val.nat)).wt = (natList (vsQVec (W *ᵥ y))).wt := rfl
    have e2 : (Val.list ([Val.nat 0] ++ (vsQVec (W *ᵥ y)).map Val.nat)).wt =
      (natList (0 :: vsQVec (W *ᵥ y))).wt := rfl
    rw [List.length_map, vsQVec_length]
    have hk : (vsQD s).succ ≤ S := by omega
    have : (vsQD s).succ * (60 * S ^ 2 + S + 40) ≤ S * (200 * S ^ 2) :=
      Nat.mul_le_mul hk (by have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; have := Nat.one_le_pow 2 S hS1; omega)
    have e3 : S * (200 * S ^ 2) = 200 * S ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (vsQD s).succ * _ ≤ 1000 * ((vsQD s).succ * (60 * S ^ 2 + S + 40)) := by
          rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ ≤ _ := by omega
  have dap := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := [a, vsQE I.p (vsQD s) 0 W]) 0)) drow)
    ((append_spec hap [.nat 0] ((vsQVec (W *ᵥ y)).map Val.nat)).mono fun w c hw =>
      ⟨hw.1, hw.2.trans (hw.1 ▸ kap)⟩)
  have dall := Det.letE dW dap
  rw [show W = X ^ vsBF I.n q from vsBWalk_eq _ _ _] at dall
  refine FunDet.intro h0 (dall.mono ?_)
  have wc := vsB_wt_ctxA hS hs hD
  have wX := vsB_wt_carA hS hs X
  have wW := vsB_wt_carA hS hs W
  have wy := vsB_wt_vecA hS hs y
  have wWy := vsB_wt_vecA hS hs (W *ᵥ y)
  have wW' := vsB_wt_carA hS hs (X ^ vsBF I.n q)
  have wWy' := vsB_wt_vecA hS hs ((X ^ vsBF I.n q) *ᵥ y)
  have wB' : (Val.list ((vsQL (X ^ vsBF I.n q)ᵀ).map natList)).wt < (vsQE I.p (vsQD s) 0 (X ^ vsBF I.n q)).wt :=
    wt_le_wt_list (by simp [vsQE])
  have w33' := wt_list3_le (.nat I.p) (.list ((vsQL (X ^ vsBF I.n q)ᵀ).map natList))
    (natList (List.replicate (vsQD s) 0))
  have w22' := wt_list2_le (.list [.nat I.p, .list ((vsQL (X ^ vsBF I.n q)ᵀ).map natList),
    natList (List.replicate (vsQD s) 0)]) (natList (vsQVec y))
  have w2a' := wt_list2_le (.list [.nat 0]) (natList (vsQVec ((X ^ vsBF I.n q) *ᵥ y)))
  have e0' : (natList (0 :: vsQVec ((X ^ vsBF I.n q) *ᵥ y))).wt =
    (Val.list ([Val.nat 0] ++ (vsQVec ((X ^ vsBF I.n q) *ᵥ y)).map Val.nat)).wt := rfl
  have eW : (vsQE I.p (vsQD s) 0 (vsBWalk I.n q X)).wt = (vsQE I.p (vsQD s) 0 (X ^ vsBF I.n q)).wt := by
    rw [vsBWalk_eq]
  have eQ : (Val.list [Val.nat I.p, natList (List.replicate (vsQD s) 0), Val.nat 0,
    Val.list (List.map natList (vsQL (X ^ vsBF I.n q)ᵀ))]).wt = (vsQE I.p (vsQD s) 0 (X ^ vsBF I.n q)).wt := rfl
  have wa := wt_list_le [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wa
  have ea : (Val.list [c, .nat q, vsQE I.p (vsQD s) 0 X, natList (vsQVec y)]).wt = a.wt := rfl
  have ec : c.wt = (vsBCtxA s hD).wt := rfl
  have wq := wt_nat_le q
  have wn := wt_nat_le I.n
  have wp := wt_nat_le I.p
  have p7 := vsQ_four_pow 7 hS1
  have p4 := vsQ_four_pow 4 hS1
  norm_num at p7 p4
  have w3 := wt_list3_le (.nat q) (vsQE I.p (vsQD s) 0 X) (.nat I.n)
  have wB : (Val.list ((vsQL Wᵀ).map natList)).wt < (vsQE I.p (vsQD s) 0 W).wt :=
    wt_le_wt_list (by simp [vsQE])
  have wz : (natList (List.replicate (vsQD s) 0)).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxA])
  have w33 := wt_list3_le (.nat I.p) (.list ((vsQL Wᵀ).map natList)) (natList (List.replicate (vsQD s) 0))
  have w22 := wt_list2_le (.list [.nat I.p, .list ((vsQL Wᵀ).map natList), natList (List.replicate (vsQD s) 0)])
    (natList (vsQVec y))
  have w2a := wt_list2_le (.list [.nat 0]) (natList (vsQVec (W *ᵥ y)))
  have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
  have wenv := wt_list2_le a (vsQE I.p (vsQD s) 0 W)
  have e0 : (natList (0 :: vsQVec (W *ᵥ y))).wt = (Val.list ([Val.nat 0] ++ (vsQVec (W *ᵥ y)).map Val.nat)).wt := rfl
  have q3 : S ^ 2 ≤ S ^ 3 := hS.pow_le (by omega)
  have q37 : S ^ 3 ≤ S ^ 7 := hS.pow_le (by omega)
  have q47 : S ^ 4 ≤ S ^ 7 := hS.pow_le (by omega)
  have q17 : S ≤ S ^ 7 := by have := hS.pow_le (show 1 ≤ 7 by omega); simpa using this
  have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le 4; have := wt_nat_le 0
  omega

include hphi in
set_option maxHeartbeats 4000000 in
/-- **The action of stage `pp`** (the hypothesis `hfa` of the transporter). -/
theorem vsB_actA_spec {pp : ℕ} (hpp : pp + 2 ≤ 4 * S) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (y : Fin (vsQD s) → ZMod I.p) :
    FunDet P (b + 1) (.list [.list [vsBCtxA s hD, .nat pp], encPerm g, natList (0 :: vsQVec y)])
      (natList (0 :: vsQVec (vsBAp s pp g y))) (Cφ + 10 ^ 18 * S ^ 7) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h1 : P.funs[b + 1]? = some (vsBActAE b (b + 4) (b + 62)) :=
    h.get (j := 1) (by rw [vsBAFuns_length]; omega)
  have ht : P.HasAt (b + 62) (linTailFuns (b + 62)) := h.block 62 rfl
  have hS1 := hS.one_le
  set c := vsBCtxA s hD
  set a := Val.list [.list [c, .nat pp], encPerm g, natList (0 :: vsQVec y)]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.list [c, .nat pp], encPerm g, natList (0 :: vsQVec y)])
    (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.list [c, .nat pp], encPerm g, natList (0 :: vsQVec y)])
    (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [.list [c, .nat pp], encPerm g, natList (0 :: vsQVec y)])
    (j := 2) rfl
  have dc := Det.get' g0 (Det.nat 0) (show [c, Val.nat pp][0]? = some c from rfl)
  have dpp := Det.get' g0 (Det.nat 1) (show [c, Val.nat pp][1]? = some (.nat pp) from rfl)
  have dq := Det.arith' (op := .add) dpp (Det.nat 2) (z := pp + 2) rfl
  have dX := Det.call (Det.mk2 dc g1) (vsB_lcar_spec h hphi hS hs hD hg)
  have dv := Det.call g2 (linTail_spec ht (.nat 0 :: (vsQVec y).map Val.nat))
  have edrop : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec y).map Val.nat)) = natList (vsQVec y) := rfl
  rw [edrop] at dv
  have dall := Det.call (Det.mk4 dc dq dX dv) (vsB_wa_spec h hS hs hD hpp (vsQLam s g) y)
  refine FunDet.intro h1 (dall.mono ?_)
  have wc := vsB_wt_ctxA hS hs hD
  have wX := vsB_wt_carA hS hs (vsQLam s g)
  have wy := vsB_wt_vecA hS hs y
  have wo := vsB_wt_vecA hS hs ((vsQLam s g ^ vsBF I.n (pp + 2)) *ᵥ y)
  have wg := hS.wt_perm g
  have ec : c.wt = (vsBCtxA s hD).wt := rfl
  have w2 := wt_list2_le c (.nat pp)
  have wa := wt_list3_le (.list [c, .nat pp]) (encPerm g) (natList (0 :: vsQVec y))
  have ea : (Val.list [.list [c, .nat pp], encPerm g, natList (0 :: vsQVec y)]).wt = a.wt := rfl
  have w4 := wt_list4_le c (.nat (pp + 2)) (vsQE I.p (vsQD s) 0 (vsQLam s g)) (natList (vsQVec y))
  have w2c := wt_list2_le c (encPerm g)
  have wpp := wt_nat_le pp
  have wpp2 := wt_nat_le (pp + 2)
  have hlt : linTailCost (Val.list (Val.nat 0 :: (vsQVec y).map Val.nat)).wt ≤ 10 ^ 8 * S ^ 6 := by
    unfold linTailCost
    have e : (Val.list (Val.nat 0 :: (vsQVec y).map Val.nat)).wt = (natList (0 :: vsQVec y)).wt := rfl
    rw [e]
    have h1 : (natList (0 :: vsQVec y)).wt + 1 ≤ 21 * S ^ 2 := by
      have := Nat.one_le_pow 2 S hS1; omega
    have := Nat.pow_le_pow_left h1 3
    have e2 : (21 * S ^ 2) ^ 3 = 9261 * S ^ 6 := by ring
    omega
  have q37 : S ^ 3 ≤ S ^ 7 := hS.pow_le (by omega)
  have q67 : S ^ 6 ≤ S ^ 7 := hS.pow_le (by omega)
  have q57 : S ^ 5 ≤ S ^ 7 := hS.pow_le (by omega)
  have q27 : S ^ 2 ≤ S ^ 7 := hS.pow_le (by omega)
  have q17 : S ≤ S ^ 7 := by have := hS.pow_le (show 1 ≤ 7 by omega); simpa using this
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have e0 : (natList (0 :: vsQVec (vsBAp s pp g y))).wt =
    (natList (0 :: vsQVec ((vsQLam s g ^ vsBF I.n (pp + 2)) *ᵥ y))).wt := rfl
  have e1 : (natList (vsQVec y)).wt = (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec y).map Val.nat))).wt := rfl
  omega

set_option maxHeartbeats 4000000 in
/-- **The point of a target unit.** -/
theorem vsB_tkA_spec {pp : ℕ} (hpp : pp + 2 ≤ 4 * S) (u : vsBU s) :
    FunDet P (b + 2) (.list [vsBCtxA s hD, .nat pp, vsQE I.p (vsQD s) 0 ((u : (vsBMt s)ˣ) : vsBMt s)])
      (natList (0 :: vsQVec (vsBTq s hD pp u))) (10 ^ 18 * S ^ 7) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h2 : P.funs[b + 2]? = some (vsBTkAE b) := h.get (j := 2) (by rw [vsBAFuns_length]; omega)
  have hS1 := hS.one_le
  set c := vsBCtxA s hD
  set U := ((u : (vsBMt s)ˣ) : vsBMt s)
  set a := Val.list [c, .nat pp, vsQE I.p (vsQD s) 0 U]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, .nat pp, vsQE I.p (vsQD s) 0 U]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, .nat pp, vsQE I.p (vsQD s) 0 U]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [c, .nat pp, vsQE I.p (vsQD s) 0 U]) (j := 2) rfl
  have de := Det.get' g0 (Det.nat 5) (show [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
      natList (List.replicate (vsQD s) 0), .nat I.n, natList (vsQVec (vsBe0 s hD))][5]? =
        some (natList (vsQVec (vsBe0 s hD))) from rfl)
  have dq := Det.arith' (op := .add) g1 (Det.nat 2) (z := pp + 2) rfl
  have dall := Det.call (Det.mk4 g0 dq g2 de) (vsB_wa_spec h hS hs hD hpp U (vsBe0 s hD))
  refine FunDet.intro h2 (dall.mono ?_)
  have wc := vsB_wt_ctxA hS hs hD
  have wX := vsB_wt_carA hS hs U
  have wy := vsB_wt_vecA hS hs (vsBe0 s hD)
  have ec : c.wt = (vsBCtxA s hD).wt := rfl
  have wa := wt_list3_le c (.nat pp) (vsQE I.p (vsQD s) 0 U)
  have ea : (Val.list [c, .nat pp, vsQE I.p (vsQD s) 0 U]).wt = a.wt := rfl
  have w4 := wt_list4_le c (.nat (pp + 2)) (vsQE I.p (vsQD s) 0 U) (natList (vsQVec (vsBe0 s hD)))
  have wo := vsB_wt_vecA hS hs ((U ^ vsBF I.n (pp + 2)) *ᵥ vsBe0 s hD)
  have wpp := wt_nat_le pp
  have wpp2 := wt_nat_le (pp + 2)
  have q37 : S ^ 3 ≤ S ^ 7 := hS.pow_le (by omega)
  have q27 : S ^ 2 ≤ S ^ 7 := hS.pow_le (by omega)
  have q17 : S ≤ S ^ 7 := by have := hS.pow_le (show 1 ≤ 7 by omega); simpa using this
  have := wt_nat_le 5; have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have e0 : (natList (0 :: vsQVec (vsBTq s hD pp u))).wt =
    (natList (0 :: vsQVec ((U ^ vsBF I.n (pp + 2)) *ᵥ vsBe0 s hD))).wt := rfl
  omega

theorem vsBPsi_inv_val {t : Perm (Fin I.n)} (ht : t ∈ gens s.hs) :
    ((((vsBPsi hs t)⁻¹ : vsBU s) : (vsBMt s)ˣ) : vsBMt s) = vsQLam s t⁻¹ := by
  simp [vsBPsi, ht]

include hphi in
set_option maxHeartbeats 4000000 in
/-- **The update** `u ↦ Λ(t)⁻¹ u`. -/
theorem vsB_upA_spec (u : vsBU s) {t : Perm (Fin I.n)} (ht : t ∈ gens s.hs) :
    FunDet P (b + 3) (.list [vsBCtxA s hD, vsQE I.p (vsQD s) 0 ((u : (vsBMt s)ˣ) : vsBMt s), encPerm t])
      (vsQE I.p (vsQD s) 0 ((((vsBPsi hs t)⁻¹ * u : vsBU s) : (vsBMt s)ˣ) : vsBMt s))
      (Cφ + 10 ^ 16 * S ^ 5) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h3 : P.funs[b + 3]? = some (vsBUpAE (b + 42) (b + 4) (b + 68)) :=
    h.get (j := 3) (by rw [vsBAFuns_length]; omega)
  have hg : P.HasAt (b + 42) (vsQGLFuns (b + 42)) := h.block 42 rfl
  have hi : P.HasAt (b + 68) (invFuns (b + 68)) := h.block 68 rfl
  have hS1 := hS.one_le
  set c := vsBCtxA s hD
  set U := ((u : (vsBMt s)ˣ) : vsBMt s)
  set a := Val.list [c, vsQE I.p (vsQD s) 0 U, encPerm t]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, vsQE I.p (vsQD s) 0 U, encPerm t]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, vsQE I.p (vsQD s) 0 U, encPerm t]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [c, vsQE I.p (vsQD s) 0 U, encPerm t]) (j := 2) rfl
  have dinv := Det.call g2 (inv_spec hi t)
  have dX := Det.call (Det.mk2 g0 dinv) (vsB_lcar_spec h hphi hS hs hD (inv_mem ht))
  have dm := Det.call (Det.mk2 dX g1) (vsQMul_spec hg (vsB_szA hS hs) (vsQLam s t⁻¹) U)
  have ev : vsQLam s t⁻¹ * U = ((((vsBPsi hs t)⁻¹ * u : vsBU s) : (vsBMt s)ˣ) : vsBMt s) := by
    rw [Subgroup.coe_mul, Units.val_mul, vsBPsi_inv_val h hS hs ht]
  rw [ev] at dm
  refine FunDet.intro h3 (dm.mono ?_)
  have wc := vsB_wt_ctxA hS hs hD
  have wX := vsB_wt_carA hS hs (vsQLam s t⁻¹)
  have wU := vsB_wt_carA hS hs U
  have wo := vsB_wt_carA hS hs ((((vsBPsi hs t)⁻¹ * u : vsBU s) : (vsBMt s)ˣ) : vsBMt s)
  have wt1 := hS.wt_perm t
  have wt2 := hS.wt_perm t⁻¹
  have ec : c.wt = (vsBCtxA s hD).wt := rfl
  have wa := wt_list3_le c (vsQE I.p (vsQD s) 0 U) (encPerm t)
  have ea : (Val.list [c, vsQE I.p (vsQD s) 0 U, encPerm t]).wt = a.wt := rfl
  have w2 := wt_list2_le c (encPerm t⁻¹)
  have w2' := wt_list2_le (vsQE I.p (vsQD s) 0 (vsQLam s t⁻¹)) (vsQE I.p (vsQD s) 0 U)
  have p5 := vsQ_four_pow 5 hS1
  have p4 := vsQ_four_pow 4 hS1
  norm_num at p5 p4
  have hn4 : (I.n + 1) ^ 4 ≤ S ^ 4 := Nat.pow_le_pow_left hS.n 4
  have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
  have q45 : S ^ 4 ≤ S ^ 5 := hS.pow_le (by omega)
  have q25 : S ^ 2 ≤ S ^ 5 := hS.pow_le (by omega)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have hik : invK * (I.n + 1) ^ 4 ≤ 100000 * S ^ 4 := Nat.mul_le_mul_left _ hn4
  have h15 : 1 ≤ S ^ 5 := Nat.one_le_pow _ _ hS1
  omega

end Specs

end GI.Impl
