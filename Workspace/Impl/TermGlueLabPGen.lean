import Workspace.Impl.TermGlueLabPHalf

/-!
# The data of one generator (step 5, program)

Step 5 of the label program (proof of Theorem A.23). For a generator `g` of the
supplement, the affine procedure takes the item `[M(ρ g), c g, M(ρ g⁻¹), c g⁻¹]`
(`tmGLAffItem`). `tmGLPGenF inv half mp` computes it on `[ctx, g]`:

1. `g⁻¹` (`inv_spec`);
2. the offset vector of `g` (`tmGLPHalf_spec` on `[ctx, [g, g⁻¹]]`);
3. the offset vector of `g⁻¹` (`tmGLPHalf_spec` on `[ctx, [g⁻¹, g]]`);
4. the two matrices (`tmGLPMPair_spec` on `[[gens N, [t, U, V, d]], [g, g⁻¹]]`);
5. the item `[M₁, c₁, M₂, c₂]`.

The result is described by `TmGLPGenOut`; the math link to `tmGLAffItem` is separate.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Algorithm (State)
open GI.Cited (Val encPerm encGroup encIntMatrix gens Membership NormalizedFactor
  ConstructiveMembership)

/-- **The item of one generator**, on `[ctx, g]`. -/
def tmGLPGenF (inv half mp : ℕ) : Expr :=
  .letE (.call inv (arg 1))
    (.letE (.call half (mk2 (arg 0) (mk2 (arg 1) (.var 1))))
      (.letE (.call half (mk2 (arg 0) (mk2 (.var 1) (arg 1))))
        (.letE (.call mp (mk2 (.get (arg 0) (.nat 0)) (mk2 (arg 1) (.var 1))))
          (mk4 (.get (.var 4) (.nat 0)) (.var 2) (.get (.var 4) (.nat 1)) (.var 3)))))

/-- **The facts of the item of `g`**: the two matrices `(U Cₖ V)ᵀ mod d` with `C₁` the
coordinates of `a ↦ g a g⁻¹` and `C₂` those of `a ↦ g⁻¹ a g`, and the offset vectors of `g`
and `g⁻¹` (`TmGLPHalfOut`). -/
def TmGLPGenOut {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σN : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ) (g : Perm (Fin m))
    (w : Val) : Prop :=
  ∃ (C₁ C₂ : Matrix (Fin σN.length) (Fin σN.length) ℤ) (v₁ v₂ : Val),
    w = .list [encIntMatrix (fun i j => (U * C₁ * V) j i % d i), v₁,
      encIntMatrix (fun i j => (U * C₂ * V) j i % d i), v₂] ∧
    (∀ j : Fin σN.length, TmGLPCoordOf σN (g * σN[j.val]'j.isLt * g⁻¹) (C₁ j)) ∧
    (∀ j : Fin σN.length, TmGLPCoordOf σN (g⁻¹ * σN[j.val]'j.isLt * g) (C₂ j)) ∧
    TmGLPHalfOut E i0 σN X V d g v₁ ∧ TmGLPHalfOut E i0 σN X V d g⁻¹ v₂

/-- The bound of the inverse, and of the weight of `g⁻¹`. -/
def tmGLPGenI (W : ℕ) : ℕ := invK * (W + 1) ^ 4

/-- The weight bound of the inputs of the inner calls. -/
def tmGLPGenW (W : ℕ) : ℕ := 2 * (W + (2 * (W + tmGLPGenI W) + 6)) + 6

/-- **The cost bound of the item of one generator.** `Y` bounds one lift; `Cs Ds Cv Dv` and
`Cc Dc Cm Dm` are the envelopes of the offset-vector and matrix-pair callees. -/
def tmGLPGenC (pm pf : Prim) (Y Cs Ds Cv Dv Cc Dc Cm Dm W : ℕ) : ℕ :=
  1000 * (W + 1) + 100 * (tmGLPGenI W + tmGLPHalfC pm pf Y Cs Ds Cv Dv (tmGLPGenW W) +
    tmGLPMPairC Cc Dc Cm Dm (tmGLPGenW W))

theorem tmGLPGenC_mono (pm pf : Prim) (Y Cs Ds Cv Dv Cc Dc Cm Dm : ℕ) {W W' : ℕ} (h : W ≤ W') :
    tmGLPGenC pm pf Y Cs Ds Cv Dv Cc Dc Cm Dm W ≤ tmGLPGenC pm pf Y Cs Ds Cv Dv Cc Dc Cm Dm W' := by
  have hI : tmGLPGenI W ≤ tmGLPGenI W' := by unfold tmGLPGenI; gcongr
  have hW : tmGLPGenW W ≤ tmGLPGenW W' := by unfold tmGLPGenW; omega
  have h1 := tmGLPHalfC_mono pm pf Y Cs Ds Cv Dv hW
  have h2 := tmGLPMPairC_mono Cc Dc Cm Dm hW
  unfold tmGLPGenC
  omega

private theorem tmGLP_g_ar {ci c1 c2 c3 c4 w1 w2 w3 w4 W I Hh Mp A1 A2 A3 : ℕ}
    (hci : ci ≤ 2 * W + 1 + 5 + 2 * I + 1)
    (hA1 : A1 ≤ 2 * W + 0 + 5 + (2 * W + 1 + 5 + (I + 1) + 4 * (W + I) + 19) +
      4 * (W + (2 * (W + I) + 6)) + 19)
    (hc1 : c1 ≤ A1 + 2 * Hh + 1)
    (hA2 : A2 ≤ 2 * W + 0 + 5 + (I + 1 + (2 * W + 1 + 5) + 4 * (I + W) + 19) +
      4 * (W + (2 * (I + W) + 6)) + 19)
    (hc2 : c2 ≤ A2 + 2 * Hh + 1)
    (hA3 : A3 ≤ 3 * W + 10 + (2 * W + 1 + 5 + (I + 1) + 4 * (W + I) + 19) +
      4 * (W + (2 * (W + I) + 6)) + 19)
    (hc3 : c3 ≤ A3 + 2 * Mp + 1)
    (hc4 : c4 ≤ 2 * (Mp + 1 + 3 + Mp + 1) + Hh + 1 + Hh + 1 + 4 * (2 * (Mp + Hh + Mp + Hh) + 8) + 9)
    (hw1 : w1 ≤ 2 * (Mp + Hh + Mp + Hh) + 8) (hw2 : w2 ≤ 2 * (Mp + Hh + Mp + Hh) + 8)
    (hw3 : w3 ≤ 2 * (Mp + Hh + Mp + Hh) + 8) (hw4 : w4 ≤ 2 * (Mp + Hh + Mp + Hh) + 8) :
    ci + (c1 + (c2 + (c3 + c4 + w1 + 1) + w2 + 1) + w3 + 1) + w4 + 1 ≤
      1000 * (W + 1) + 100 * (I + Hh + Mp) := by
  omega

set_option maxHeartbeats 1000000 in
/-- **The item of one generator.** On `[ctx, g]`, the result is `[M₁, c₁, M₂, c₂]` with the
facts `TmGLPGenOut`. The hypotheses are those of `tmGLPHalf_spec` for `g` and for `g⁻¹`, and
those of `tmGLPMPair_spec`. -/
theorem tmGLPGen_spec (hm : Membership) (hfac : NormalizedFactor) (hcm : ConstructiveMembership)
    {P : Program} {f inv half mp off lb xs ov : ℕ} (hf : P.funs[f]? = some (tmGLPGenF inv half mp))
    (hinv : P.HasAt inv (invFuns inv)) (hhalf : P.funs[half]? = some (tmGLPHalfF off (lb + 1) xs ov))
    (hoffA : TmGLPOffAt P off hm hfac) {hst : GI.Cited.PointwiseStab}
    (hlA : TmGLPL1At P lb hst hfac) (hxsA : TmGLPXsAt P xs) (hovA : TmGLPOVecAt P ov hcm)
    (hmpA : TmGLPMPairAt P mp hcm)
    {Ce De Cs Ds Cv Dv Cc Dc Cm Dm : ℕ} (hEB : ∀ W, linElementBudget hcm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    (hCM : ∀ W, tmGLPCMatC Ce De W ≤ Cc * (W + 2) ^ Dc)
    (hMC : ∀ W t, tmGLPMatC W t ≤ Cm * (W + 0 + t + 2) ^ Dm)
    -- the lift
    {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GI.Algorithm.GiantLabels S}
    {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom)
    (hnat : GI.Algorithm.NaturalRows S L label) (hE : ∀ b i, label (E (b, i)) = i)
    (i0 : Fin L.q) {ps' : List (Perm (Fin k) × Perm (Fin m))}
    (hps' : Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range)
    {Y : ℕ} (hY : tmGLPL1C (normalizedFactorPrim hfac) (ps'.length + k + k + L.q + 2) ≤ Y)
    -- the row transporters
    {Ω' : Type} [GI.Multicoset.RAct (Perm (Fin m)) Ω'] {H : Subgroup (Perm (Fin m))}
    {σN : List (Perm (Fin m))} (hNH : gens σN ≤ H) (hn : GI.Multicoset.Normalizes H (gens σN))
    {X Z : Fin L.q → Ω'} {vs : List Val} (hT : TmCsTabOK H X Z vs)
    (hZ : ∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso H (X j) (Z l)).Nonempty)
    {xl : List Val} (hxl : TmGLPXOut (gens σN) X (.list xl))
    (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ)
    -- the generator
    (g : Perm (Fin m)) (hD : g ∈ GI.Multicoset.Aut H (GI.Multicoset.types (gens σN) X))
    (hs : ∀ h, h = g ∨ h = g⁻¹ →
      ∃ y : Fin L.q → Perm (Fin m), GI.Paper.cleanRowPerm E y ∈ S.domGroup ∧ y i0 = h)
    (hyN : ∀ h, h = g ∨ h = g⁻¹ → ∀ y : Fin L.q → Perm (Fin m),
      GI.Paper.cleanRowPerm E y ∈ S.domGroup → y i0 = h⁻¹ → ∀ i, h * y i ∈ gens σN)
    (hs1 : ∀ a ∈ σN, g * a * g⁻¹ ∈ gens σN) (hs2 : ∀ a ∈ σN, g⁻¹ * a * g ∈ gens σN) :
    FunAll P f (.list [tmGLPHCtx σN U V d vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]),
        encPerm g])
      (fun w c => TmGLPGenOut E i0 σN X U V d g w ∧
        c ≤ tmGLPGenC (membershipPrim hm) (normalizedFactorPrim hfac) Y Cs Ds Cv Dv Cc Dc Cm Dm
          (Val.list [tmGLPHCtx σN U V d vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]),
            encPerm g]).wt) := by
  obtain ⟨cm, mat, mcj, cj, cp, tl, mec, ec, jm, mul, tr, red, hmp, hcm', hcp, hcj, hmcj, htl,
    hmec, hec, hmat, hmul, htr, hred⟩ := hmpA
  set pm := membershipPrim hm
  set pf := normalizedFactorPrim hfac
  set mc0 : Val := .list [encGroup σN, tmGLPMCtx U V d] with hmc0
  set cx : Val := tmGLPHCtx σN U V d vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E])
    with hcx
  set a : Val := .list [cx, encPerm g] with ha
  set W := a.wt with hW
  obtain ⟨I, hI⟩ : ∃ I, tmGLPGenI W = I := ⟨_, rfl⟩
  obtain ⟨Hh, hHh⟩ : ∃ Hh, tmGLPHalfC pm pf Y Cs Ds Cv Dv (tmGLPGenW W) = Hh := ⟨_, rfl⟩
  obtain ⟨Mp, hMp⟩ : ∃ Mp, tmGLPMPairC Cc Dc Cm Dm (tmGLPGenW W) = Mp := ⟨_, rfl⟩
  have hGW : tmGLPGenW W = 2 * (W + (2 * (W + I) + 6)) + 6 := by rw [tmGLPGenW, hI]
  have hGW' : tmGLPGenW W = 2 * (W + (2 * (I + W) + 6)) + 6 := by rw [hGW]; omega
  unfold tmGLPGenC
  rw [hI, hHh, hMp]
  have wcx : cx.wt < W := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp)
  have wmc : mc0.wt < cx.wt := by
    have : mc0.wt < (Val.list [mc0, .list [encGroup σN, .list vs, .nat L.q, .list xl],
      .list [liftLabCtx k m ps', coordsVal e S E]]).wt := wt_le_wt_list (by simp)
    exact this
  have hmW : m < W := (tmGLP_n_lt_wt g).trans wg
  have hinvS : FunDet P inv (encPerm g) (encPerm g⁻¹) I := by
    refine (inv_spec hinv g).mono ?_
    rw [← hI]; unfold tmGLPGenI
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val), [cx, encPerm g][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  -- the two half calls, as specifications
  have hH1 := tmGLPHalf_spec hm hfac hcm hhalf hoffA hlA hxsA hovA hEB hCS hVC E hnat hE i0 hps'
    hY hNH hn hT hZ hxl U V d g (hD := (GI.Multicoset.Aut H _).inv_mem hD)
    (hs _ (Or.inr rfl)) (fun y hy hy0 => hyN g (Or.inl rfl) y hy hy0)
  have hH2 := tmGLPHalf_spec hm hfac hcm hhalf hoffA hlA hxsA hovA hEB hCS hVC E hnat hE i0 hps'
    hY hNH hn hT hZ hxl U V d g⁻¹ (hD := by rw [inv_inv]; exact hD)
    (by rw [inv_inv]; exact hs _ (Or.inl rfl))
    (fun y hy hy0 => hyN g⁻¹ (Or.inr rfl) y hy hy0)
  rw [inv_inv] at hH2
  have hMS := tmGLPMPair_spec hcm hmp hcm' hcp hcj hmcj htl hmec hec hmat hmul htr hred hEB hCM
    hMC σN U V d g hs1 hs2
  clear_value a W
  apply FunAll.intro hf
  -- step 1: the inverse
  have g1 : Det P [a] (arg 1) (encPerm g) (2 * W + 1 + 5) := gA _ _ _ rfl
  have c0 := tmGLP_call_le g1 le_rfl hinvS le_rfl
  refine EvalAll.letE c0.1 fun v1 ci h1 => ?_
  obtain ⟨rfl, hci⟩ := h1
  -- step 2: the offset vector of `g`
  have g0a : Det P [a, encPerm g⁻¹] (arg 0) cx (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1a : Det P [a, encPerm g⁻¹] (arg 1) (encPerm g) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dv1a := Det.var' (P := P) (env := [a, encPerm g⁻¹]) (i := 1) rfl
  have p1 := tmGLP_mk2_le g1a le_rfl dv1a (B := I + 1) (by omega) (X := W) (Y := I) wg.le c0.2.le
  have p1' := tmGLP_mk2_le g0a le_rfl p1.1 le_rfl (X := W) (Y := 2 * (W + I) + 6) wcx.le p1.2
  have c1 := tmGLP_callAll_le p1'.1 le_rfl (C := Hh) (R := TmGLPHalfOut E i0 σN X V d g)
    (FunAll.mono hH1 fun w c h => ⟨h.1, h.2.trans (by
      rw [← hHh]; exact tmGLPHalfC_mono _ _ _ _ _ _ _ (by rw [hGW]; exact p1'.2))⟩)
  refine EvalAll.letE c1 fun v2 c1' h2 => ?_
  obtain ⟨hv2, hc1, hw2⟩ := h2
  -- step 3: the offset vector of `g⁻¹`
  have g0b : Det P [a, encPerm g⁻¹, v2] (arg 0) cx (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1b : Det P [a, encPerm g⁻¹, v2] (arg 1) (encPerm g) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dv1b := Det.var' (P := P) (env := [a, encPerm g⁻¹, v2]) (i := 1) rfl
  have p2 := tmGLP_mk2_le dv1b (A := I + 1) (by omega) g1b le_rfl (X := I) (Y := W) c0.2.le wg.le
  have p2' := tmGLP_mk2_le g0b le_rfl p2.1 le_rfl (X := W) (Y := 2 * (I + W) + 6) wcx.le p2.2
  have c2 := tmGLP_callAll_le p2'.1 le_rfl (C := Hh) (R := TmGLPHalfOut E i0 σN X V d g⁻¹)
    (FunAll.mono hH2 fun w c h => ⟨h.1, h.2.trans (by
      rw [← hHh]; exact tmGLPHalfC_mono _ _ _ _ _ _ _ (by rw [hGW']; exact p2'.2))⟩)
  refine EvalAll.letE c2 fun v3 c2' h3 => ?_
  obtain ⟨hv3, hc2, hw3⟩ := h3
  -- step 4: the matrices
  have g0c : Det P [a, encPerm g⁻¹, v2, v3] (arg 0) cx (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1c : Det P [a, encPerm g⁻¹, v2, v3] (arg 1) (encPerm g) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dMc := Det.get' g0c (Det.nat 0)
    (vs := [mc0, .list [encGroup σN, .list vs, .nat L.q, .list xl],
      .list [liftLabCtx k m ps', coordsVal e S E]]) (v := mc0) rfl
  have dv1c := Det.var' (P := P) (env := [a, encPerm g⁻¹, v2, v3]) (i := 1) rfl
  have p3 := tmGLP_mk2_le g1c le_rfl dv1c (B := I + 1) (by omega) (X := W) (Y := I) wg.le c0.2.le
  have p3' := tmGLP_mk2_le dMc (A := 3 * W + 10) (by omega) p3.1 le_rfl (X := W)
    (Y := 2 * (W + I) + 6) (by omega) p3.2
  have c3 := tmGLP_callAll_le p3'.1 le_rfl (C := Mp)
    (R := fun w => ∃ C₁ C₂ : Matrix (Fin σN.length) (Fin σN.length) ℤ,
      w = .list [encIntMatrix (fun i j => (U * C₁ * V) j i % d i),
        encIntMatrix (fun i j => (U * C₂ * V) j i % d i)] ∧
      (∀ j : Fin σN.length, TmGLPCoordOf σN (g * σN[j.val]'j.isLt * g⁻¹) (C₁ j)) ∧
      (∀ j : Fin σN.length, TmGLPCoordOf σN (g⁻¹ * σN[j.val]'j.isLt * g) (C₂ j)))
    (FunAll.mono hMS fun w c h => by
      obtain ⟨C₁, C₂, hw, h1, h2, hc⟩ := h
      exact ⟨⟨C₁, C₂, hw, h1, h2⟩, hc.trans (by
        rw [← hMp]; exact tmGLPMPairC_mono _ _ _ _ (by rw [hGW]; exact p3'.2))⟩)
  refine EvalAll.letE c3 fun v4 c3' h4 => ?_
  obtain ⟨⟨C₁, C₂, rfl, hC₁, hC₂⟩, hc3, hw4⟩ := h4
  -- step 5: the item
  set M₁ := encIntMatrix (fun i j => (U * C₁ * V) j i % d i) with hM₁
  set M₂ := encIntMatrix (fun i j => (U * C₂ * V) j i % d i) with hM₂
  have wM₁ : M₁.wt < Mp := (wt_le_wt_list (by simp)).trans hw4
  have wM₂ : M₂.wt < Mp := (wt_le_wt_list (by simp)).trans hw4
  have env4 : [a, encPerm g⁻¹, v2, v3, Val.list [M₁, M₂]][4]? = some (Val.list [M₁, M₂]) := rfl
  have d4 := Det.var' (P := P) env4
  have dg0 := Det.get' d4 (Det.nat 0) (vs := [M₁, M₂]) (v := M₁) rfl
  have dg1 := Det.get' d4 (Det.nat 1) (vs := [M₁, M₂]) (v := M₂) rfl
  have dv2 := Det.var' (P := P) (env := [a, encPerm g⁻¹, v2, v3, Val.list [M₁, M₂]]) (i := 2) rfl
  have dv3 := Det.var' (P := P) (env := [a, encPerm g⁻¹, v2, v3, Val.list [M₁, M₂]]) (i := 3) rfl
  have d5 := Det.mk4 dg0 dv2 dg1 dv3
  have w5 := wt_list4_le M₁ v2 M₂ v3
  have hw5 : (Val.list [M₁, v2, M₂, v3]).wt ≤ 2 * (Mp + Hh + Mp + Hh) + 8 := by omega
  refine d5.post fun c4 hc4 => ⟨⟨C₁, C₂, v2, v3, rfl, hC₁, hC₂, hv2, hv3⟩, ?_⟩
  have hc4' : c4 ≤ 2 * (Mp + 1 + 3 + Mp + 1) + Hh + 1 + Hh + 1 +
      4 * (2 * (Mp + Hh + Mp + Hh) + 8) + 9 := by omega
  exact tmGLP_g_ar hci le_rfl hc1 le_rfl hc2 le_rfl hc3 hc4' hw5 hw5 hw5 hw5

end GI.Impl
