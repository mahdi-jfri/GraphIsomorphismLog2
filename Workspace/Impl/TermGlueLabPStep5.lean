module

public import Workspace.Impl.TermGlueLabPSetP

@[expose] public section

/-!
# Step 5 of the label program: the context and the items

Step 5 of the label program (proof of Theorem A.23). `tmGLPStep5F set items` runs
the setup program (`tmGLPSet_spec`) for the context `ctx = [t, U, V, d]` and then the per-generator
program over the generators `gs` of the supplement (`map`, `tmGLPItems_spec`). On
`[[gens N*, gens N, [b_j]], [gens N, vs, q, xl], lc, [g for g in gs]]` it returns
`[ctx, items]`, the data that step 6 encodes into `tmGLAffIn` (`TmGLPStep5Out`; the items are
`tmGLAffItem` by `tmGLP_items_eq` and `tmGLP_gen_item`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Algorithm (State)
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens FullRankInst fullRankInput)

/-- **Step 5**, on `[[gens N*, gens N, [b_j]], [gens N, vs, q, xl], lc, [g]]`. -/
def tmGLPStep5F (set items : ℕ) : Expr :=
  .letE (.call set (arg 0))
    (mk2 (.var 1) (.call items (mk2 (mk3 (mk2 (.get (arg 0) (.nat 1)) (.var 1)) (arg 1) (arg 2))
      (arg 3))))

/-- The input of step 5. -/
def tmGLPStep5In {m : ℕ} (σS σN bs : List (Perm (Fin m))) (vs : List Val) (q : ℕ) (xl : List Val)
    (lc : Val) (gs : List (Perm (Fin m))) : Val :=
  .list [.list [encGroup σS, encGroup σN, .list (bs.map encPerm)],
    .list [encGroup σN, .list vs, .nat q, .list xl], lc, .list (gs.map encPerm)]

/-- **The output of step 5**: `[ctx, items]` with the setup facts for `ctx = [t, U, V, d]` and,
for every generator `g`, an item related to `g` by `R U V d`. -/
def TmGLPStep5OutR {m : ℕ} (σS σN bs : List (Perm (Fin m)))
    (R : Matrix (Fin σN.length) (Fin σN.length) ℤ → Matrix (Fin σN.length) (Fin σN.length) ℤ →
      (Fin σN.length → ℤ) → Perm (Fin m) → Val → Prop)
    (gs : List (Perm (Fin m))) (w : Val) : Prop :=
  ∃ (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) (Z : Matrix (Fin bs.length) (Fin σN.length) ℤ)
    (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (ws : List Val),
    w = .list [tmGLPMCtx U V (fun i => D i i), .list ws] ∧ linPermPresentation σS σN M ∧
    (∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j)) ∧ IsUnit V.det ∧
    (∀ i, 0 < D i i) ∧
    (∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i) ∧
    U * V = 1 ∧ V * U = 1 ∧
    List.Forall₂ (fun g w => R U V (fun i => D i i) g w) gs ws

/-- The output of step 5 with the items of `tmGLPGen_spec`. -/
def TmGLPStep5Out {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σS σN bs : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (gs : List (Perm (Fin m))) (w : Val) : Prop :=
  TmGLPStep5OutR σS σN bs (TmGLPGenOut E i0 σN X) gs w

/-- The weight bound of the input of the `map`. -/
def tmGLPStep5W (SC W : ℕ) : ℕ := 20 * (W + SC) + 50

/-- **The cost bound of step 5**, for a setup bound `SC` and a per-item bound `G`. -/
def tmGLPStep5C (SC : ℕ → ℕ) (G : ℕ → ℕ) (W : ℕ) : ℕ :=
  1000 * (W + 1) + 100 * (SC W + tmGLPItemsC G (tmGLPStep5W (SC W) W))

set_option maxHeartbeats 1000000 in
/-- **Step 5.** With the setup program at `set` (cost at most `SC` of the weight of its input,
`SC` monotone) and a per-generator program at `gen` (any `U, V, d`; cost at most `G`, monotone;
`tmGLPGen_spec` gives it), `tmGLPStep5F set items` returns `[ctx, items]` with `TmGLPStep5Out`. -/
theorem tmGLPStep5R_spec {P : Program} {f set items gen : ℕ}
    (hf : P.funs[f]? = some (tmGLPStep5F set items)) (hitems : P.HasAt items (mapFuns items gen))
    {q m : ℕ} (σS σN bs : List (Perm (Fin m)))
    (R : Matrix (Fin σN.length) (Fin σN.length) ℤ → Matrix (Fin σN.length) (Fin σN.length) ℤ →
      (Fin σN.length → ℤ) → Perm (Fin m) → Val → Prop)
    (vs : List Val) (xl : List Val) (lc : Val) (gs : List (Perm (Fin m)))
    {SC G : ℕ → ℕ} (hSC : Monotone SC) (hG : Monotone G)
    (hset : FunAll P set (.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]) (fun w c =>
      TmGLPSetOut σS σN bs w ∧ c ≤ SC (Val.list [encGroup σS, encGroup σN,
        .list (bs.map encPerm)]).wt))
    (hgen : ∀ (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ),
      ∀ g ∈ gs, FunAll P gen (.list [tmGLPHCtx σN U V d vs q xl lc, encPerm g]) (fun w c =>
        R U V d g w ∧
          c ≤ G (Val.list [tmGLPHCtx σN U V d vs q xl lc, encPerm g]).wt)) :
    FunAll P f (tmGLPStep5In σS σN bs vs q xl lc gs) (fun w c =>
      TmGLPStep5OutR σS σN bs R gs w ∧
        c ≤ tmGLPStep5C SC G (tmGLPStep5In σS σN bs vs q xl lc gs).wt) := by
  set s0 : Val := .list [encGroup σS, encGroup σN, .list (bs.map encPerm)] with hs0
  set oc : Val := .list [encGroup σN, .list vs, .nat q, .list xl] with hoc
  set gl : Val := .list (gs.map encPerm) with hgl
  set a : Val := tmGLPStep5In σS σN bs vs q xl lc gs with ha
  set W := a.wt with hW
  obtain ⟨Sc, hSc⟩ : ∃ Sc, SC W = Sc := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, tmGLPItemsC G (tmGLPStep5W Sc W) = T := ⟨_, rfl⟩
  unfold tmGLPStep5C
  rw [hSc, hT]
  have w0 : s0.wt < W := by
    have : s0.wt < (Val.list [s0, oc, lc, gl]).wt := wt_le_wt_list (by simp)
    exact this
  have w1 : oc.wt < W := by
    have : oc.wt < (Val.list [s0, oc, lc, gl]).wt := wt_le_wt_list (by simp)
    exact this
  have w2 : lc.wt < W := by
    have : lc.wt < (Val.list [s0, oc, lc, gl]).wt := wt_le_wt_list (by simp)
    exact this
  have w3 : gl.wt < W := by
    have : gl.wt < (Val.list [s0, oc, lc, gl]).wt := wt_le_wt_list (by simp)
    exact this
  have wN : (encGroup σN).wt < s0.wt := wt_le_wt_list (by simp)
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val), [s0, oc, lc, gl][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  have hset' : FunAll P set s0 (fun w c => TmGLPSetOut σS σN bs w ∧ c ≤ Sc) :=
    FunAll.mono hset fun w c h => ⟨h.1, h.2.trans (by rw [← hSc]; exact hSC w0.le)⟩
  clear_value a W
  apply FunAll.intro hf
  have c1 := tmGLP_callAll_le (gA [] 0 _ rfl) le_rfl hset'
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨⟨M, Z, U, V, D, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU⟩, hc1, hv1⟩ := h1
  set ctx := tmGLPMCtx U V (fun i => D i i) with hctx
  -- the input of the map
  have g0 := gA [ctx] 0 _ rfl
  have dN := Det.get' g0 (Det.nat 1) (vs := [encGroup σS, encGroup σN, .list (bs.map encPerm)])
    (v := encGroup σN) rfl
  have dv1 := Det.var' (P := P) (env := [a, ctx]) (i := 1) rfl
  have p1 := tmGLP_mk2_le dN (A := 3 * W + 10) (by omega) dv1 (B := Sc + 1) (by omega)
    (X := W) (Y := Sc) (by omega) hv1.le
  have p2 := Det.mk3 p1.1 (gA [ctx] 1 _ rfl) (gA [ctx] 2 _ rfl)
  have wp2 := wt_list3_le (.list [encGroup σN, ctx]) oc lc
  have p3 := tmGLP_mk2_le p2 le_rfl (gA [ctx] 3 _ rfl) le_rfl
    (X := 2 * (2 * (W + Sc) + 6 + W + W) + 7) (Y := W) (by omega) w3.le
  have hin : (Val.list [tmGLPHCtx σN U V (fun i => D i i) vs q xl lc, gl]).wt ≤
      tmGLPStep5W Sc W := by
    have := p3.2
    change (Val.list [.list [.list [encGroup σN, ctx], oc, lc], gl]).wt ≤ _
    unfold tmGLPStep5W; omega
  have hmap := tmGLPItems_spec hitems encPerm_injective gs hG
    (R := fun g w => R U V (fun i => D i i) g w)
    (hgen U V (fun i => D i i))
  have c2 := tmGLP_callAll_le (vin := .list [tmGLPHCtx σN U V (fun i => D i i) vs q xl lc, gl])
    p3.1 le_rfl (C := T)
    (R := fun w => ∃ ws, w = .list ws ∧
      List.Forall₂ (fun g w => R U V (fun i => D i i) g w) gs ws)
    (FunAll.mono hmap fun w c ⟨ws, hw, hws, hc⟩ => ⟨⟨ws, hw, hws⟩, hc.trans (by
      rw [← hT]; exact tmGLPItemsC_mono hG hin)⟩)
  refine (EvalAll.mk2_last dv1 c2).mono fun w c h => ?_
  obtain ⟨vb, cb, ⟨⟨ws, rfl, hws⟩, hcb, hvb⟩, rfl, hc⟩ := h
  refine ⟨⟨M, Z, U, V, D, ws, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩, ?_⟩
  have hw := wt_list2_le ctx (Val.list ws)
  have hcb' : cb ≤ 100 * W + 40 * Sc + 2 * T + 300 := by omega
  have hfin : c ≤ Sc + 1 + cb + 2 * (2 * (Sc + T) + 6) + 7 := by omega
  have hwf : (Val.list [ctx, Val.list ws]).wt ≤ 2 * (Sc + T) + 6 := by omega
  omega

/-- **Step 5** with the per-generator program of `tmGLPGen_spec`. -/
theorem tmGLPStep5_spec {P : Program} {f set items gen : ℕ}
    (hf : P.funs[f]? = some (tmGLPStep5F set items)) (hitems : P.HasAt items (mapFuns items gen))
    {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σS σN bs : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (vs : List Val) (xl : List Val) (lc : Val) (gs : List (Perm (Fin m)))
    {SC G : ℕ → ℕ} (hSC : Monotone SC) (hG : Monotone G)
    (hset : FunAll P set (.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]) (fun w c =>
      TmGLPSetOut σS σN bs w ∧ c ≤ SC (Val.list [encGroup σS, encGroup σN,
        .list (bs.map encPerm)]).wt))
    (hgen : ∀ (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ),
      ∀ g ∈ gs, FunAll P gen (.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]) (fun w c =>
        TmGLPGenOut E i0 σN X U V d g w ∧
          c ≤ G (Val.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]).wt)) :
    FunAll P f (tmGLPStep5In σS σN bs vs L.q xl lc gs) (fun w c =>
      TmGLPStep5Out E i0 σS σN bs X gs w ∧
        c ≤ tmGLPStep5C SC G (tmGLPStep5In σS σN bs vs L.q xl lc gs).wt) :=
  tmGLPStep5R_spec hf hitems σS σN bs (TmGLPGenOut E i0 σN X) vs xl lc gs hSC hG hset hgen

end GI.Impl

namespace GI.Impl

/-! ### Polynomial bound of the matrix pair -/

theorem tmGLPMPX_poly (Cc Dc : ℕ) : PBU (fun _ W _ => tmGLPMPX Cc Dc W) := by
  unfold tmGLPMPX
  exact PBU.smul Cc (PBU.pow (PBU.addc (PBU.smul 64 PBU.W) 202) Dc)

theorem tmGLPMPZ_poly (Cc Dc Cm Dm : ℕ) : PBU (fun _ W _ => tmGLPMPZ Cc Dc Cm Dm W) := by
  have hf : PBU (fun _ W _ => Cm * (W + 8) ^ Dm) := PBU.smul Cm (PBU.pow (PBU.addc PBU.W 8) Dm)
  have hg := tmGLP_pbu_lin (tmGLPMPX_poly Cc Dc) 3 0 0
  refine (tmGLP_pbu_subst hf hg).mono fun _ W _ => le_of_eq ?_
  unfold tmGLPMPZ
  congr 3
  omega

/-- **`tmGLPMPairC` is polynomial** (the bound of `tmGLPMPair_spec` and `tmGLPOVec_spec`). -/
theorem tmGLPMPairC_poly (Cc Dc Cm Dm : ℕ) : PBU (fun _ W _ => tmGLPMPairC Cc Dc Cm Dm W) := by
  have h := PBU.add (PBU.add (PBU.smul 1000 (PBU.addc PBU.W 1))
    (PBU.smul 40 (tmGLPMPX_poly Cc Dc))) (PBU.smul 40 (tmGLPMPZ_poly Cc Dc Cm Dm))
  exact h.mono fun _ _ _ => le_of_eq rfl

end GI.Impl
