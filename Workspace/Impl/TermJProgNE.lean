module

public import Workspace.Impl.TermJProgOut

@[expose] public section

/-!
# The `J`-answer for a nonempty label answer (program)

`tmJNEF`, on `[V, w]` with the input `V` of `TermJSpec` and a nonempty label answer
`w = [h₀, ⟨U⟩]`, runs the four steps of the paper's last paragraph of the proof of
Theorem A.23:

1. the context of the per-label program (`tmJ_prep_spec`);
2. a transporter `t_h` for each label `h ∈ h₀ · (1 :: U)` (`tmJ_labs_spec` with the per-label
   function);
3. the generators of `Aut_J(x)` (`tmJ_aut_spec`);
4. the answer `[t₀, red(t₀⁻¹ t_h, Aut_J)]` (`tmJ_out_spec`), on `Fin (m q)`.

`tmJ_ne_spec` is generic in the relation `Rl` that the per-label function meets; the caller
proves the per-label hypotheses for every possible context.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens encIntMatrix GroupOrder ConstructiveMembership
  NormalizedIntersection HermiteFullRank PointwiseStab)
open scoped IsMulCommutative

/-- On `[V, w]`. -/
def tmJNEF (pr lb au ou : ℕ) : Expr :=
  .letE (.call pr (arg 0))
  (.letE (.call lb (mk2 (.var 1) (arg 1)))
  (.letE (.call au (mk2 (.var 1) (.get (arg 0) (.nat 1))))
  (.call ou (mk3 (.var 2) (.var 3)
    (.arith .mul (.get (.get (.var 1) (.nat 10)) (.nat 3))
      (.get (.get (.var 1) (.nat 10)) (.nat 2)))))))

/-- Where the pieces of `tmJNEF` sit; `pb` is the per-label function. -/
structure TmJNEAt (P : Program) (f pr lb au ou pb jo jm jni jh jst : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJNEF pr lb au ou)
  hpr : ∃ pa mk lg tl bt lac, TmJPrepAt P pr pa mk lg tl bt lac jo jm
  hlb : ∃ mpC cp mpH, P.funs[lb]? = some (tmJLabsF mpC mpH) ∧
    P.HasAt mpC (mapFuns mpC cp) ∧ P.HasAt cp (composeFuns cp) ∧ P.HasAt mpH (mapFuns mpH pb)
  hau : ∃ ns ker s2 ts sw app, TmJAutAt P au ns ker s2 ts sw app jni jh
  hou : ∃ iv mpC cp app mk rd, TmJOutAt P ou iv mpC cp app mk rd jst

theorem tmJLabsK_mono (KH DH : ℕ) : Monotone (tmJLabsK KH DH) := by
  intro a b h
  unfold tmJLabsK
  gcongr

theorem tmJOutK_mono (p : Prim) : Monotone (tmJOutK p) := by
  intro a b h
  unfold tmJOutK Prim.boundSize
  gcongr

/-- The bound of `tmJNEF`. -/
def tmJNEK (Kp Dp KH DH Ka Da : ℕ) (p : Prim) (W : ℕ) : ℕ :=
  1000 * (W + Kp * (W + 1) ^ Dp +
    tmJLabsK KH DH (2 * (Kp * (W + 1) ^ Dp + W) + 6) +
    Ka * (2 * (Kp * (W + 1) ^ Dp + W) + 7) ^ Da +
    tmJOutK p (2 * (tmJLabsK KH DH (2 * (Kp * (W + 1) ^ Dp + W) + 6) +
      Ka * (2 * (Kp * (W + 1) ^ Dp + W) + 7) ^ Da +
      Kp * (W + 1) ^ Dp * (Kp * (W + 1) ^ Dp) + 2) + 7) + 100)

theorem tmJNEK_poly (Kp Dp KH DH Ka Da : ℕ) (p : Prim) : TmJPoly (tmJNEK Kp Dp KH DH Ka Da p) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hP : TmJPoly fun W => Kp * (W + 1) ^ Dp :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add hW (TmJPoly.const 1)) _)
  have hI : TmJPoly fun W => 2 * (Kp * (W + 1) ^ Dp + W) + 6 :=
    TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add hP hW)) (TmJPoly.const 6)
  have hL : TmJPoly fun W => tmJLabsK KH DH (2 * (Kp * (W + 1) ^ Dp + W) + 6) :=
    TmJPoly.comp_mono (tmJLabsK_poly KH DH) (tmJLabsK_mono KH DH) hI
  have hA : TmJPoly fun W => Ka * (2 * (Kp * (W + 1) ^ Dp + W) + 7) ^ Da :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add hP hW))
      (TmJPoly.const 7)) _)
  have hO : TmJPoly fun W => tmJOutK p (2 * (tmJLabsK KH DH (2 * (Kp * (W + 1) ^ Dp + W) + 6) +
      Ka * (2 * (Kp * (W + 1) ^ Dp + W) + 7) ^ Da +
      Kp * (W + 1) ^ Dp * (Kp * (W + 1) ^ Dp) + 2) + 7) :=
    TmJPoly.comp_mono (tmJOutK_poly p) (tmJOutK_mono p)
      (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add (TmJPoly.add (TmJPoly.add hL hA)
        (TmJPoly.mul hP hP)) (TmJPoly.const 2))) (TmJPoly.const 7))
  unfold tmJNEK
  exact TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add hW hP)
    hL) hA) hO) (TmJPoly.const 100))

/-- A list related entrywise to a list of labels by a relation whose values are permutation
codes is a list of permutation codes. -/
theorem tmJ_forall₂_perms {α : Type*} {n : ℕ} {R : α → Val → Prop}
    (hR : ∀ a v, R a v → ∃ τ : Perm (Fin n), v = encPerm τ) :
    ∀ {l : List α} {ws : List Val}, List.Forall₂ R l ws →
      ∃ τs : List (Perm (Fin n)), ws = τs.map encPerm
  | [], [], _ => ⟨[], rfl⟩
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    obtain ⟨τ, rfl⟩ := hR _ _ h
    obtain ⟨τs, rfl⟩ := tmJ_forall₂_perms hR t
    exact ⟨τ :: τs, rfl⟩

private theorem tmJNE_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- **The `J`-answer for a nonempty label answer.** -/
theorem tmJ_ne_spec (ho : GroupOrder) (hcm : ConstructiveMembership)
    (hni : NormalizedIntersection) (hH : HermiteFullRank) (hst : PointwiseStab) (KH DH : ℕ) :
    ∃ K D : ℕ, ∀ {P : Program} {f pr lb au ou pb jo jm jni jh jst : ℕ},
      TmJNEAt P f pr lb au ou pb jo jm jni jh jst →
      P.prims[jo]? = some (groupOrderPrim ho) → P.prims[jm]? = some (linMembershipPrim hcm) →
      P.prims[jni]? = some (normalizedIntersectionPrim hni) →
      P.prims[jh]? = some (linHermitePrim hH) → P.prims[jst]? = some (pointwiseStabPrim hst) →
      ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {sv : Val},
      Canon e c sv S → ∀ {m q : ℕ} (E : Fin m × Fin q ≃ S.dom),
      (domFin e S.dom).length = m * q → 0 < q →
      ∀ (σH σN σS : List (Equiv.Perm (Fin m))), gens σS ≤ gens σN →
      (∀ x ∈ gens σN, ∀ y ∈ gens σN, x * y * x⁻¹ * y⁻¹ ∈ gens σS) →
      ∀ [((gens σS).subgroupOf (gens σN)).Normal]
        [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))]
        (O : Fin q → Fin q → Option (Equiv.Perm (Fin m) × List (Equiv.Perm (Fin m)))),
      (∀ a, ∃ r gs, O a a = some (r, gs) ∧ GI.Multicoset.Normalizes (gens gs) (gens σS)) →
      ∀ (us : List Val), (∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) →
      (∀ p ∈ tmJLgList O, p.2 ∈ gens σN) →
      ∀ (vs : List Val) (lv rl : Val) (h0 : Equiv.Perm (Fin m)) (U : List (Equiv.Perm (Fin m)))
        (Rl : List (Equiv.Perm (Fin k)) → Equiv.Perm (Fin m) → Val → Prop),
      (∀ gs h out, Rl gs h out → ∃ τ : Equiv.Perm (Fin (m * q)), out = encPerm τ) →
      (∀ (gs : List (Equiv.Perm (Fin k)))
          (Bm : Matrix (Fin (tmJLgList O).length) (Fin σN.length) ℤ)
          (M : Matrix (Fin σN.length) (Fin σN.length) ℤ),
        gens gs = groupFin e S.G →
        (∀ k', tmJHF σS σN (Bm k') = Additive.ofMul (QuotientGroup.mk'
          ((gens σS).subgroupOf (gens σN))
          (linIntoSubgroup (gens σN) ((tmJLgList O).get k').2))) →
        linPresentationCertificate M (tmJHF σS σN) →
        ∀ h ∈ tmJLabs h0 U, FunAll P pb (.list [tmJHCtx (tmJGList e S E gs)
            ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
            vs σS σN (tmJLgList O) (tmJTlList O) Bm M, encPerm h]) (fun out cst =>
          Rl gs h out ∧ cst ≤ KH * ((Val.list [tmJHCtx (tmJGList e S E gs)
            ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
            vs σS σN (tmJLgList O) (tmJTlList O) Bm M, encPerm h]).wt + 1) ^ DH)) →
      FunAll P f (.list [.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us,
          .list vs], .list [encPerm h0, encGroup U]])
        (fun out cost => (∃ (gs : List (Equiv.Perm (Fin k)))
            (Bm : Matrix (Fin (tmJLgList O).length) (Fin σN.length) ℤ)
            (M : Matrix (Fin σN.length) (Fin σN.length) ℤ),
            gens gs = groupFin e S.G ∧
            (∀ k', tmJHF σS σN (Bm k') = Additive.ofMul (QuotientGroup.mk'
              ((gens σS).subgroupOf (gens σN))
              (linIntoSubgroup (gens σN) ((tmJLgList O).get k').2))) ∧
            linPresentationCertificate M (tmJHF σS σN) ∧
            ∃ (τ0 : Equiv.Perm (Fin (m * q))) (τs : List (Equiv.Perm (Fin (m * q)))),
              List.Forall₂ (Rl gs) (tmJLabs h0 U) ((τ0 :: τs).map encPerm) ∧
            ∃ al : List (Equiv.Perm (Fin m × Fin q)),
              tmJAutOut O σS σN (tmJLgList O) (tmJTlList O) Bm M (tmJPermsVal al) ∧
            ∃ hs : List (Equiv.Perm (Fin (m * q))), out = .list [encPerm τ0, encGroup hs] ∧
              gens hs = gens ((τ0 :: τs).map (τ0⁻¹ * ·) ++
                al.map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))) ∧
              hs.length ≤ (m * q) ^ 2) ∧
          cost ≤ K * ((Val.list [.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl],
            .list us, .list vs], .list [encPerm h0, encGroup U]]).wt + 1) ^ D) := by
  obtain ⟨Kp, Dp, hPrep⟩ := tmJ_prep_spec ho hcm
  obtain ⟨Ka, Da, hAut⟩ := tmJ_aut_spec hni hH
  obtain ⟨K, D, hKD⟩ := tmJNEK_poly Kp Dp KH DH Ka Da (pointwiseStabPrim hst)
  refine ⟨K, D, ?_⟩
  intro P f pr lb au ou pb jo jm jni jh jst hA hjo hjm hjni hjh hjst Ω C k e c S sv hsv m q E hs
    hq σH σN σS hle hcomm _ _ O hlocN us hus hlgN vs lv rl h0 U Rl hRl hLab
  obtain ⟨pa, mk, lg, tl, bt, lac, hPA⟩ := hA.hpr
  obtain ⟨mpC, cp, mpH, hlbf, hmpC, hcp, hmpH⟩ := hA.hlb
  obtain ⟨ns, ker, s2, ts, sw, app, hAA⟩ := hA.hau
  obtain ⟨iv, mpC', cp', app', mk', rd, hOA⟩ := hA.hou
  refine FunAll.intro hA.hf ?_
  unfold tmJNEF
  set V := Val.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us,
    .list vs] with hV
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [V, .list [encPerm h0, encGroup U]]).wt = W := ⟨_, rfl⟩
  rw [hW]
  have wV : V.wt < W := hW ▸ wt_le_wt_list (by simp)
  have ww : (Val.list [encPerm h0, encGroup U]).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wus : (Val.list us).wt < V.wt := wt_le_wt_list (by simp)
  -- the bounds
  obtain ⟨Bp, hBp⟩ : ∃ Bp, Kp * (W + 1) ^ Dp = Bp := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl, tmJLabsK KH DH (2 * (Bp + W) + 6) = Bl := ⟨_, rfl⟩
  obtain ⟨Ba, hBa⟩ : ∃ Ba, Ka * (2 * (Bp + W) + 7) ^ Da = Ba := ⟨_, rfl⟩
  obtain ⟨Bq, hBq⟩ : ∃ Bq, Bp * Bp = Bq := ⟨_, rfl⟩
  obtain ⟨Bo, hBo⟩ : ∃ Bo, tmJOutK (pointwiseStabPrim hst) (2 * (Bl + Ba + Bq + 2) + 7) = Bo :=
    ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb, W + Bp + Bl + Ba + Bo + 100 = Sb := ⟨_, rfl⟩
  have hK : tmJNEK Kp Dp KH DH Ka Da (pointwiseStabPrim hst) W = 1000 * Sb := by
    unfold tmJNEK; rw [← hSb, ← hBo, ← hBq, ← hBa, ← hBl, ← hBp]
  have hfin : 1000 * Sb ≤ K * (W + 1) ^ D := hK ▸ hKD W
  -- step 1: the context
  have dP := hPrep hPA hjo hjm e c hsv E hs hq σH σN σS hle hcomm O
    (fun a => by obtain ⟨r, gs, h, -⟩ := hlocN a; exact ⟨r, gs, h⟩) us hus hlgN vs lv rl
  have dP' := dP.mono (Q' := fun w cst => (∃ (gs : List (Equiv.Perm (Fin k)))
      (Bm : Matrix (Fin (tmJLgList O).length) (Fin σN.length) ℤ)
      (M : Matrix (Fin σN.length) (Fin σN.length) ℤ),
      gens gs = groupFin e S.G ∧
      (∀ k', tmJHF σS σN (Bm k') = Additive.ofMul (QuotientGroup.mk'
        ((gens σS).subgroupOf (gens σN))
        (linIntoSubgroup (gens σN) ((tmJLgList O).get k').2))) ∧
      linPresentationCertificate M (tmJHF σS σN) ∧
      w = tmJHCtx (tmJGList e S E gs)
        ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
        vs σS σN (tmJLgList O) (tmJTlList O) Bm M) ∧ cst ≤ Bp) fun w cst h =>
    ⟨h.1, h.2.trans (by
      rw [← hBp, ← hV]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))⟩
  have a0 := (Det.arg' (P := P) (vs := [V, .list [encPerm h0, encGroup U]]) (rest := [])
    (j := 0) (v := V) rfl).mono (c' := 20 * Sb) (by rw [hW]; omega)
  refine (tmJ_letCall (C := 150 * Sb) a0 dP' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro ctxV ⟨gs, Bm, M, hgs, hBm, hM, rfl⟩ wctx
  set CT := tmJHCtx (tmJGList e S E gs)
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
    vs σS σN (tmJLgList O) (tmJTlList O) Bm M with hCT
  have wlc : (tmJLocCtx m q).wt < CT.wt := wt_le_wt_list (by simp [hCT, tmJHCtx])
  have hm1 : m < (tmJLocCtx m q).wt :=
    (tmJNE_lt_wt (1 : Equiv.Perm (Fin m))).trans (wt_le_wt_list (by simp [tmJLocCtx]))
  have hq1 : q < (tmJLocCtx m q).wt :=
    (tmJNE_lt_wt (1 : Equiv.Perm (Fin q))).trans (wt_le_wt_list (by simp [tmJLocCtx]))
  have hmq : m * q ≤ Bq := by
    rw [← hBq]; exact Nat.mul_le_mul (by omega) (by omega)
  have wCT : CT.wt < Bp := wctx
  -- step 2: the label transporters
  have dL := tmJ_labs_spec KH DH hlbf hmpC hcp hmpH CT h0 U (Rl gs)
    (fun h hh => hLab gs Bm M hgs hBm hM h hh)
  have wLin : (Val.list [CT, .list [encPerm h0, encGroup U]]).wt ≤ 2 * (Bp + W) + 6 := by
    have := wt_list2_le CT (.list [encPerm h0, encGroup U]); omega
  have dL' := dL.mono (Q' := fun w cst => (∃ ws, w = .list ws ∧
      List.Forall₂ (Rl gs) (tmJLabs h0 U) ws) ∧ cst ≤ Bl) fun w cst h =>
    ⟨h.1, h.2.trans (by rw [← hBl]; exact tmJLabsK_mono KH DH wLin)⟩
  have b1 := Det.var' (P := P) (env := [Val.list [V, .list [encPerm h0, encGroup U]], CT]) (i := 1)
    (v := CT) rfl
  have b2 := Det.arg' (P := P) (vs := [V, .list [encPerm h0, encGroup U]]) (rest := [CT]) (j := 1)
    (v := .list [encPerm h0, encGroup U]) rfl
  have cL := (Det.mk2 b1 b2).mono (c' := 10 * Sb) (by rw [hW]; omega)
  refine (tmJ_letCall (C := 60 * Sb) cL dL' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro tsV ⟨ws, rfl, hws⟩ wts
  obtain ⟨τl, rfl⟩ := tmJ_forall₂_perms (hRl gs) hws
  obtain ⟨τ0, τs, rfl⟩ : ∃ τ0 τs, τl = τ0 :: τs := by
    cases τl with
    | nil => exact absurd hws (by simp [tmJLabs])
    | cons τ0 τs => exact ⟨τ0, τs, rfl⟩
  -- step 3: the generators of `Aut_J`
  have dA := hAut hAA hjni hjh (tmJGList e S E gs)
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
    vs σS σN (tmJLgList O) (tmJTlList O) Bm M hM.1 O us hus hlocN
  have wAin : (Val.list [CT, .list us]).wt + 1 ≤ 2 * (Bp + W) + 7 := by
    have := wt_list2_le CT (.list us); omega
  have dA' := dA.mono (Q' := fun w cst =>
      tmJAutOut O σS σN (tmJLgList O) (tmJTlList O) Bm M w ∧ cst ≤ Ba) fun w cst h =>
    ⟨h.1, h.2.trans (by
      rw [← hBa]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wAin _))⟩
  have d1 := Det.var' (P := P) (env := [Val.list [V, .list [encPerm h0, encGroup U]], CT,
    .list ((τ0 :: τs).map encPerm)]) (i := 1) (v := CT) rfl
  have d0 := Det.arg' (P := P) (vs := [V, .list [encPerm h0, encGroup U]])
    (rest := [CT, .list ((τ0 :: τs).map encPerm)]) (j := 0) (v := V) rfl
  have dus := Det.get' d0 (Det.nat 1)
    (vs := [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us, .list vs])
    (v := .list us) rfl
  have cA := (Det.mk2 d1 dus).mono (c' := 10 * Sb) (by
    have := wt_list2_le CT (.list us); rw [hW]; omega)
  refine (tmJ_letCall (C := 20 * Sb) cA dA' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro ajV ⟨hsA, Ks, hA1, hA2, hA3, rfl⟩ waj
  -- step 4: the answer
  obtain ⟨al, hal⟩ : ∃ al, tmJNsList hsA ++ Ks.map (tmJLam (tmJLgList O)) ++
      tmJS3List (tmJTlList O) = al := ⟨_, rfl⟩
  rw [hal] at waj ⊢
  have hal' : tmJPermsVal al = .list ((al.map (toFin (finProdFinEquiv :
      Fin m × Fin q ≃ Fin (m * q)))).map encPerm) := by
    simp only [tmJPermsVal, List.map_map, Function.comp_def]
  have dO := tmJ_out_spec hst hOA hjst τ0 τs (al.map (toFin (finProdFinEquiv :
      Fin m × Fin q ≃ Fin (m * q))))
  rw [← hal'] at dO
  have wOin : (Val.list [.list ((τ0 :: τs).map encPerm), tmJPermsVal al, .nat (m * q)]).wt ≤
      2 * (Bl + Ba + Bq + 2) + 7 := by
    have := wt_list3_le (.list ((τ0 :: τs).map encPerm)) (tmJPermsVal al) (.nat (m * q))
    have := wt_nat_le (m * q)
    omega
  have dO' := dO.mono (Q' := fun w cst => (∃ hs : List (Equiv.Perm (Fin (m * q))),
      w = .list [encPerm τ0, encGroup hs] ∧
      gens hs = gens ((τ0 :: τs).map (τ0⁻¹ * ·) ++
        al.map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))) ∧
      hs.length ≤ (m * q) ^ 2) ∧ cst ≤ Bo) fun w cst h =>
    ⟨h.1, h.2.trans (by rw [← hBo]; exact tmJOutK_mono _ wOin)⟩
  have hBoq : 2 * (Bl + Ba + Bq + 2) + 7 ≤ Bo := by
    rw [← hBo]; unfold tmJOutK; omega
  have env3 : ∀ i (v : Val), [Val.list [V, .list [encPerm h0, encGroup U]], CT,
      .list ((τ0 :: τs).map encPerm), tmJPermsVal al][i]? = some v →
      Det P [Val.list [V, .list [encPerm h0, encGroup U]], CT, .list ((τ0 :: τs).map encPerm),
        tmJPermsVal al] (.var i) v (v.wt + 1) := fun i v hv => Det.var' hv
  have f1 := env3 1 CT rfl
  have flc := Det.get' f1 (Det.nat 10) (vs := [encGroup (tmJGList e S E gs),
    encGroup ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
    .list vs, .list (σN.map encPerm), encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
    tmJTlVal (tmJTlList O), encIntMatrix Bm, encIntMatrix M, tmJLocCtx m q])
    (v := tmJLocCtx m q) rfl
  have fm := Det.get' flc (Det.nat 3) (vs := [encPerm (1 : Equiv.Perm (Fin m)),
    encPerm (1 : Equiv.Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have fq := Det.get' flc (Det.nat 2) (vs := [encPerm (1 : Equiv.Perm (Fin m)),
    encPerm (1 : Equiv.Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have fmq := Det.arith' (op := .mul) fm fq (z := m * q) rfl
  have cO := (Det.mk3 (env3 2 _ rfl) (env3 3 _ rfl) fmq).mono (c' := 10 * Sb) (by
    have := wt_list3_le (.list ((τ0 :: τs).map encPerm)) (tmJPermsVal al) (.nat (m * q))
    have := wt_nat_le (m * q)
    have := wt_nat_le m
    have := wt_nat_le q
    have := wt_nat_le 10
    have : (tmJLocCtx m q).wt < CT.wt := wlc
    omega)
  refine (tmJ_lastCall cO dO').mono fun u cu hu => ⟨⟨gs, Bm, M, hgs, hBm, hM, τ0, τs, hws, al,
    ⟨hsA, Ks, hA1, hA2, hA3, by rw [hal]⟩, hu.1⟩, by omega⟩

end GI.Impl
