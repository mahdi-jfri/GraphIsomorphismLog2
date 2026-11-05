module

public import Workspace.Impl.TermGlueLabPOEps

@[expose] public section

/-!
# The item of one generator with the orientation coordinate (step 5, program)

Step 5 of the label program, the case where all types are distinct.
`tmGLPGenOF inv eps gen cons blk` computes, on `[ctx, g]`:
1. `g⁻¹`;
2. the orientation entries `ε(g⁻¹)` and `ε(g)` (`tmGLPEps_spec` at `g` and at `g⁻¹`);
3. the item `[M₁, c₁, M₂, c₂]` without the orientation (`tmGLPGen_spec`);
4. the item `[[[1,0],[0,M₁]], (ε(g⁻¹), c₁), [[1,0],[0,M₂]], (ε(g), c₂)]`
   (`tmGLPBlk_spec`, `tmGLPCons_spec`).
`tmGLPGenO_spec`: the result has the facts `TmGLPGenOOut`; it is the contract's item by
`tmGLP_genO_item`.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Algorithm (State)
open GI.Cited (Val encInt encPerm encGroup encIntMatrix gens)

/-- **The item of one generator with the orientation coordinate**, on `[ctx, g]`. -/
def tmGLPGenOF (inv eps gen cons blk : ℕ) : Expr :=
  .letE (.call inv (arg 1))
    (.letE (.call eps (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
      (.letE (.call eps (mk2 (.get (arg 0) (.nat 1)) (.var 1)))
        (.letE (.call gen (.var 0))
          (mk4 (.call blk (.get (.var 4) (.nat 0)))
            (.call cons (mk2 (.var 2) (.get (.var 4) (.nat 1))))
            (.call blk (.get (.var 4) (.nat 2)))
            (.call cons (mk2 (.var 3) (.get (.var 4) (.nat 3))))))))

/-- The cost bound; `G` bounds the item without the orientation, `Ep` one orientation entry. -/
def tmGLPGenOC (G Ep : ℕ → ℕ) (W : ℕ) : ℕ :=
  1000 * (W + 1) + 100 * (tmGLPGenI W + Ep (tmGLPGenW W) + G W + tmGLPBlkC (G W) +
    tmGLPConsC (2 * G W + 206))

theorem tmGLPBlkC_mono {W W' : ℕ} (h : W ≤ W') : tmGLPBlkC W ≤ tmGLPBlkC W' := by
  unfold tmGLPBlkC; gcongr

theorem tmGLPGenOC_mono {G Ep : ℕ → ℕ} (hG : Monotone G) (hEp : Monotone Ep) :
    Monotone (tmGLPGenOC G Ep) := by
  intro W W' h
  have hI : tmGLPGenI W ≤ tmGLPGenI W' := by unfold tmGLPGenI; gcongr
  have hW : tmGLPGenW W ≤ tmGLPGenW W' := by unfold tmGLPGenW; omega
  have h1 := hEp hW
  have h2 := hG h
  have h3 := tmGLPBlkC_mono h2
  have h4 := tmGLPConsC_mono (show 2 * G W + 206 ≤ 2 * G W' + 206 by omega)
  unfold tmGLPGenOC
  omega

set_option maxHeartbeats 1000000 in
/-- **The item of one generator with the orientation coordinate.** -/
theorem tmGLPGenO_spec {P : Program} {f inv eps gen cons blk app : ℕ}
    (hf : P.funs[f]? = some (tmGLPGenOF inv eps gen cons blk))
    (hinv : P.HasAt inv (invFuns inv)) (hcons : P.funs[cons]? = some (tmGLPConsF app))
    (happ : P.HasAt app (appendFuns app)) (hblk : P.HasAt blk (tmGLPBlkFuns blk))
    {G Ep : ℕ → ℕ} (hEp : Monotone Ep)
    {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σN : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ)
    (vs xl : List Val) (lc : Val) (g : Perm (Fin m))
    (hgen : FunAll P gen (.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]) (fun w c =>
      TmGLPGenOut E i0 σN X U V d g w ∧
        c ≤ G (Val.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]).wt))
    (heps : ∀ h, h = g ∨ h = g⁻¹ →
      FunAll P eps (.list [.list [encGroup σN, .list vs, .nat L.q, .list xl], encPerm h])
        (fun w c => w = encInt (tmGLPEc (gens σN) X h⁻¹ : ℤ) ∧
          c ≤ Ep (Val.list [.list [encGroup σN, .list vs, .nat L.q, .list xl], encPerm h]).wt)) :
    FunAll P f (.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]) (fun w c =>
      TmGLPGenOOut E i0 σN X U V d g w ∧
        c ≤ tmGLPGenOC G Ep (Val.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]).wt) := by
  set mc : Val := .list [encGroup σN, tmGLPMCtx U V d] with hmc
  set c1 : Val := .list [encGroup σN, .list vs, .nat L.q, .list xl] with hc1
  set cx : Val := tmGLPHCtx σN U V d vs L.q xl lc with hcx
  set a : Val := .list [cx, encPerm g] with ha
  set W := a.wt with hW
  obtain ⟨I, hI⟩ : ∃ I, tmGLPGenI W = I := ⟨_, rfl⟩
  obtain ⟨Pe, hPe⟩ : ∃ Pe, Ep (tmGLPGenW W) = Pe := ⟨_, rfl⟩
  obtain ⟨Gw, hGw⟩ : ∃ Gw, G W = Gw := ⟨_, rfl⟩
  obtain ⟨Bk, hBk⟩ : ∃ Bk, tmGLPBlkC Gw = Bk := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn, tmGLPConsC (2 * Gw + 206) = Cn := ⟨_, rfl⟩
  have hGW : tmGLPGenW W = 2 * (W + (2 * (W + I) + 6)) + 6 := by rw [tmGLPGenW, hI]
  unfold tmGLPGenOC
  rw [hI, hPe, hGw, hBk, hCn]
  have wcx : cx.wt < W := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp)
  have wc1 : c1.wt < cx.wt := by
    have : c1.wt < (Val.list [mc, c1, lc]).wt := wt_le_wt_list (by simp)
    exact this
  have hmW : m < W := (tmGLP_n_lt_wt g).trans wg
  have hinvS : FunDet P inv (encPerm g) (encPerm g⁻¹) I := by
    refine (inv_spec hinv g).mono ?_
    rw [← hI]; unfold tmGLPGenI
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hwi : (encPerm g⁻¹).wt < I := tmGLP_fundet_wt hinvS
  -- the two orientation entries, as deterministic calls
  have he1 : FunDet P eps (.list [c1, encPerm g]) (encInt (tmGLPEc (gens σN) X g⁻¹ : ℤ)) Pe := by
    refine FunAll.mono (heps g (Or.inl rfl)) fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans ?_⟩
    rw [← hPe]; refine hEp ?_
    have := wt_list2_le c1 (encPerm g); rw [hGW]; omega
  have he2 : FunDet P eps (.list [c1, encPerm g⁻¹]) (encInt (tmGLPEc (gens σN) X g : ℤ)) Pe := by
    refine FunAll.mono (heps g⁻¹ (Or.inr rfl)) fun w c ⟨hw, hc⟩ => ⟨by rw [hw, inv_inv], hc.trans ?_⟩
    rw [← hPe]; refine hEp ?_
    have := wt_list2_le c1 (encPerm g⁻¹); rw [hGW]; omega
  have wE1 := tmGLP_encEc_wt (gens σN) X g⁻¹
  have wE2 := tmGLP_encEc_wt (gens σN) X g
  set E1 := encInt (tmGLPEc (gens σN) X g⁻¹ : ℤ) with hE1
  set E2 := encInt (tmGLPEc (gens σN) X g : ℤ) with hE2
  have hgen' : FunAll P gen a (fun w c => (TmGLPGenOut E i0 σN X U V d g w ∧ c ≤ Gw) ∧ w.wt < c) :=
    FunAll.wt_lt (FunAll.mono hgen fun w c h => ⟨h.1, h.2.trans_eq hGw⟩)
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val), [cx, encPerm g][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  clear_value a W
  apply FunAll.intro hf
  -- the inverse
  have g1 : Det P [a] (arg 1) (encPerm g) (2 * W + 1 + 5) := gA [] 1 _ rfl
  have c0 := tmGLP_call_le g1 le_rfl hinvS le_rfl
  refine EvalAll.letE c0.1 fun v1 ci h1 => ?_
  obtain ⟨rfl, hci⟩ := h1
  -- the entry of `g⁻¹`
  have gx1 : Det P [a, encPerm g⁻¹] (arg 0) (.list [mc, c1, lc]) (2 * W + 0 + 5) :=
    gA [encPerm g⁻¹] 0 _ rfl
  have gc1 : Det P [a, encPerm g⁻¹] (.get (arg 0) (.nat 1)) c1 (2 * W + 0 + 5 + (1 + 3) + c1.wt + 1) :=
    Det.get' gx1 (Det.nat 1) (x := 1) (vs := [mc, c1, lc]) rfl
  have ga1 : Det P [a, encPerm g⁻¹] (arg 1) (encPerm g) (2 * W + 1 + 5) :=
    gA [encPerm g⁻¹] 1 _ rfl
  have p1 := tmGLP_mk2_le gc1 le_rfl ga1 le_rfl (X := W) (Y := W) (by omega) wg.le
  have q1 := tmGLP_call_le p1.1 le_rfl he1 le_rfl
  refine EvalAll.letE q1.1 fun v2 ce1 h2 => ?_
  obtain ⟨rfl, hce1⟩ := h2
  -- the entry of `g`
  have gx2 : Det P [a, encPerm g⁻¹, E1] (arg 0) (.list [mc, c1, lc]) (2 * W + 0 + 5) :=
    gA [encPerm g⁻¹, E1] 0 _ rfl
  have gc2 : Det P [a, encPerm g⁻¹, E1] (.get (arg 0) (.nat 1)) c1 (2 * W + 0 + 5 + (1 + 3) + c1.wt + 1) :=
    Det.get' gx2 (Det.nat 1) (x := 1) (vs := [mc, c1, lc]) rfl
  have gv1 : Det P [a, encPerm g⁻¹, E1] (.var 1) (encPerm g⁻¹) ((encPerm g⁻¹).wt + 1) :=
    Det.var' rfl
  have p2 := tmGLP_mk2_le gc2 le_rfl gv1 le_rfl (X := W) (Y := I) (by omega) hwi.le
  have q2 := tmGLP_call_le p2.1 le_rfl he2 le_rfl
  refine EvalAll.letE q2.1 fun v3 ce2 h3 => ?_
  obtain ⟨rfl, hce2⟩ := h3
  -- the item without the orientation
  have gv0 : Det P [a, encPerm g⁻¹, E1, E2] (.var 0) a (a.wt + 1) := Det.var' rfl
  refine EvalAll.letE (EvalAll.call_funAll gv0 (Q := fun w c => TmGLPGenOut E i0 σN X U V d g w ∧
      c ≤ W + 1 + Gw + Gw + 1 ∧ w.wt < Gw) fun v ca hv => ?_) fun v4 cg h4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    exact hgen'.mono fun w c ⟨⟨hR, hc⟩, hw⟩ => ⟨hR, by omega, by omega⟩
  obtain ⟨hR, hcg, hw4⟩ := h4
  have hR' := hR
  obtain ⟨C₁, C₂, v₁, v₂, rfl, hC₁, hC₂, h₁, h₂⟩ := hR'
  obtain ⟨_, _, _, _, _, _, _, _, hv₁⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _, _, hv₂⟩ := h₂
  set M₁ : Matrix (Fin σN.length) (Fin σN.length) ℤ := fun i j => (U * C₁ * V) j i % d i
  set M₂ : Matrix (Fin σN.length) (Fin σN.length) ℤ := fun i j => (U * C₂ * V) j i % d i
  set r : Val := .list [encIntMatrix M₁, v₁, encIntMatrix M₂, v₂] with hr
  obtain ⟨l₁, rfl⟩ : ∃ l₁, v₁ = .list l₁ := ⟨_, hv₁⟩
  obtain ⟨l₂, rfl⟩ : ∃ l₂, v₂ = .list l₂ := ⟨_, hv₂⟩
  have wm1 : (encIntMatrix M₁).wt < Gw := (wt_le_wt_list (by simp)).trans hw4
  have wm2 : (encIntMatrix M₂).wt < Gw := (wt_le_wt_list (by simp)).trans hw4
  have wl1 : (Val.list l₁).wt < Gw := (wt_le_wt_list (by simp)).trans hw4
  have wl2 : (Val.list l₂).wt < Gw := (wt_le_wt_list (by simp)).trans hw4
  set env : List Val := [a, encPerm g⁻¹, E1, E2, r] with henv
  have dr : Det P env (.var 4) r (r.wt + 1) := Det.var' rfl
  -- the four entries
  have hb1 := (tmGLPBlk_spec hblk M₁).mono (tmGLPBlkC_mono wm1.le)
  have hb2 := (tmGLPBlk_spec hblk M₂).mono (tmGLPBlkC_mono wm2.le)
  rw [hBk] at hb1 hb2
  have k1 := tmGLP_call_le (Det.get' dr (Det.nat 0) (x := 0) (vs := [encIntMatrix M₁, .list l₁,
    encIntMatrix M₂, .list l₂]) rfl) le_rfl hb1 le_rfl
  have k3 := tmGLP_call_le (Det.get' dr (Det.nat 2) (x := 2) (vs := [encIntMatrix M₁, .list l₁,
    encIntMatrix M₂, .list l₂]) rfl) le_rfl hb2 le_rfl
  have hk2 := (tmGLPCons_spec hcons happ E1 l₁).mono (tmGLPConsC_mono (show
    (Val.list [E1, .list l₁]).wt ≤ 2 * Gw + 206 by have := wt_list2_le E1 (.list l₁); omega))
  have hk4 := (tmGLPCons_spec hcons happ E2 l₂).mono (tmGLPConsC_mono (show
    (Val.list [E2, .list l₂]).wt ≤ 2 * Gw + 206 by have := wt_list2_le E2 (.list l₂); omega))
  rw [hCn] at hk2 hk4
  have m2 := tmGLP_mk2_le (Det.var' (P := P) (env := env) (i := 2) (v := E1) rfl) le_rfl
    (Det.get' dr (Det.nat 1) (x := 1) (vs := [encIntMatrix M₁, .list l₁, encIntMatrix M₂, .list l₂]) rfl)
    le_rfl (X := 100) (Y := Gw) wE1 wl1.le
  have m4 := tmGLP_mk2_le (Det.var' (P := P) (env := env) (i := 3) (v := E2) rfl) le_rfl
    (Det.get' dr (Det.nat 3) (x := 3) (vs := [encIntMatrix M₁, .list l₁, encIntMatrix M₂, .list l₂]) rfl)
    le_rfl (X := 100) (Y := Gw) wE2 wl2.le
  have k2 := tmGLP_call_le m2.1 le_rfl hk2 le_rfl
  have k4 := tmGLP_call_le m4.1 le_rfl hk4 le_rfl
  have dm := Det.mk4 k1.1 k2.1 k3.1 k4.1
  refine dm.post fun c hc => ⟨⟨C₁, C₂, .list l₁, .list l₂, hR, rfl⟩, ?_⟩
  -- the cost
  have w4 := wt_list4_le (encIntMatrix (tmGLPBlk M₁)) (.list (E1 :: l₁))
    (encIntMatrix (tmGLPBlk M₂)) (.list (E2 :: l₂))
  have wr : r.wt < Gw := hw4
  have hp1 := p1.2
  have hp2 := p2.2
  have hc1l : c1.wt < W := wc1.trans wcx
  have hwgi := hwi
  have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
  have : (Val.nat 3).wt ≤ 5 := wt_nat_le 3
  have hk1 := k1.2
  have hk2' := k2.2
  have hk3 := k3.2
  have hk4' := k4.2
  have hm2 := m2.2
  have hm4 := m4.2
  have hq1 := q1.2
  have hq2 := q2.2
  clear_value M₁ M₂ r env E1 E2
  clear hb1 hb2 hk2 hk4 he1 he2 hgen' hinvS hgen heps k1 k2 k3 k4 m2 m4 q1 q2 p1 p2 dm c0
  omega

end GI.Impl
