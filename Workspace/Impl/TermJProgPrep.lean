module

public import Workspace.Impl.TermJProgPrepA
public import Workspace.Impl.TermJProgBeta
public import Workspace.Impl.TermJProgTl
public import Workspace.Impl.TermJHSpec
public import Workspace.Impl.LinAbelianCoordinates

@[expose] public section

/-!
# The context of the per-label program (program)

`tmJPrepF`, on the input `V = [[sv, lv, cv, a18, rl], us, vs]` of `TermJSpec` (without `r`
and the label answer), computes the context `tmJHCtx …` that the per-label program
`tmJH_spec` reads:

1. the groups `G|_dom`, `N^q` and the local context (`tmJ_prepA_spec`);
2. group values of `N* = ⟨σS⟩` and `N = ⟨σN⟩` (`mkGroup_spec`);
3. the pairs `lg` of the stored local generators and the triples `Tl` (`tmJ_lg_spec`,
   `tmJ_tl_spec`);
4. the coordinate vectors `β_k` of the generators in `lg` (`tmJ_beta_spec`; paper, proof of
   Theorem A.23: "the coordinate vectors of the stored generators of `Aut_N(z_a)`");
5. a presentation matrix `M` of `A = N/N*` (`linAbelianCoordinates_spec_poly`, with the
   abelian coordinates of the proof of Theorem A.20).

`tmJ_prep_spec` states the result; its cost is polynomial in the input weight.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens encIntMatrix GroupOrder ConstructiveMembership)
open scoped IsMulCommutative

/-- A list of expressions, built from the last entry to the first: `tmJMkR [e₂, e₁, e₀]` is
`[e₀, e₁, e₂]`. -/
def tmJMkR : List Expr → Expr
  | [] => .nil
  | e :: es => .snoc (tmJMkR es) e

theorem tmJ_mkR_det {P : Program} {env : List Val} {c Wb : ℕ} :
    ∀ (es : List Expr) (vs : List Val), List.Forall₂ (fun e v => Det P env e v c) es vs →
      (Val.list vs.reverse).wt ≤ Wb →
      Det P env (tmJMkR es) (.list vs.reverse) (es.length * (c + Wb + 1) + 5)
  | [], [], _, _ => by simpa [tmJMkR] using Det.nil
  | e :: es, v :: vs, h, hW => by
    obtain ⟨he, hes⟩ := List.forall₂_cons.1 h
    have hpre : (Val.list vs.reverse).wt ≤ Wb :=
      (wt_list_mono ⟨[v], by simp⟩).trans hW
    have ih := tmJ_mkR_det es vs hes hpre
    have hs := Det.snoc ih he
    rw [List.reverse_cons]
    refine hs.mono ?_
    rw [List.reverse_cons] at hW
    simp only [List.length_cons]
    rw [Nat.add_mul, one_mul]
    omega

/-- On `V = [[sv, lv, cv, a18, rl], us, vs]`: the context of the per-label program. -/
def tmJPrepF (pa mk lg tl bt lac : ℕ) : Expr :=
  .letE (.call pa (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))
    (.get (.get (arg 0) (.nat 3)) (.nat 1))))
  (.letE (.call mk (mk2 (.get (.get (.var 1) (.nat 2)) (.nat 3))
    (.get (.get (arg 0) (.nat 3)) (.nat 2))))
  (.letE (.call mk (mk2 (.get (.get (.var 1) (.nat 2)) (.nat 3))
    (.get (.get (arg 0) (.nat 3)) (.nat 1))))
  (.letE (.call lg (mk2 (arg 1) (.get (.get (.var 1) (.nat 2)) (.nat 2))))
  (.letE (.call tl (mk2 (arg 1) (.get (.get (.var 1) (.nat 2)) (.nat 2))))
  (.letE (.call bt (mk3 (.var 2) (.var 3) (.var 4)))
  (.letE (.call lac (mk2 (.var 2) (.var 3)))
  (tmJMkR [.get (.var 1) (.nat 2), .var 7, .var 6, .var 5, .var 4, .var 3, .var 2,
    .get (.get (arg 0) (.nat 3)) (.nat 1), arg 2, .get (.var 1) (.nat 1),
    .get (.var 1) (.nat 0)])))))))

/-- Where the pieces of `tmJPrepF` sit. -/
structure TmJPrepAt (P : Program) (f pa mk lg tl bt lac jo jm : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJPrepF pa mk lg tl bt lac)
  hpa : ∃ tab gg rg nq, TmJPrepAAt P pa tab gg rg mk nq
  hmk : P.HasAt mk (mkGroupFuns mk)
  hlg : ∃ rg tbR row mp e fl app, TmJLgAt P lg rg tbR row mp e fl app
  htl : ∃ rg tbE e fl app, TmJTlAt P tl rg tbE e fl app
  hbt : ∃ mp e vv, P.funs[bt]? = some (tmJBetaF mp vv) ∧ P.HasAt mp (mapFuns mp e) ∧
    P.funs[e]? = some tmJLgPEF ∧ P.HasAt vv (tmJVVecsFuns vv jm)
  hlac : P.HasAt lac (linAbelianCoordinatesFuns lac jo jm)

/-- The bound of `tmJPrepF`, in the weight `W` of its input and the constants of the two
cited steps. -/
def tmJPrepK (Kb Db Kl Dl W : ℕ) : ℕ :=
  10 ^ 6 * (W + tmJPrepAK (2 * W + 7) +
    2 * (mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3) +
    tmJLgK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) + tmJTlK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) +
    Kb * (4 * (mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3) +
      2 * tmJLgK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) + 9) ^ Db +
    Kl * (4 * (mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3) + 7) ^ Dl + 100)

theorem tmJPrepAK_mono : Monotone tmJPrepAK := by
  intro a b h
  unfold tmJPrepAK tmCsTabK tmJGK tmJNqK
  gcongr

theorem tmJPrepK_poly (Kb Db Kl Dl : ℕ) : TmJPoly (tmJPrepK Kb Db Kl Dl) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hA : TmJPoly fun W => tmJPrepAK (2 * W + 7) :=
    TmJPoly.comp_mono tmJPrepAK_poly tmJPrepAK_mono
      (TmJPoly.add (TmJPoly.smul 2 hW) (TmJPoly.const 7))
  have hA1 : TmJPoly fun W => tmJPrepAK (2 * W + 7) + 1 := TmJPoly.add hA (TmJPoly.const 1)
  have hS : TmJPoly fun W => mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3 :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.mul (TmJPoly.add hW (TmJPoly.const 2)) hA1) 3)
  have hL : TmJPoly fun W => tmJLgK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) := by
    unfold tmJLgK; exact TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add hW (TmJPoly.pow hA1 2)) _)
  have hT : TmJPoly fun W => tmJTlK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) := by
    unfold tmJTlK; exact TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add hW (TmJPoly.pow hA1 2)) _)
  have hB : TmJPoly fun W => Kb * (4 * (mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3) +
      2 * tmJLgK (W + (tmJPrepAK (2 * W + 7) + 1) ^ 2) + 9) ^ Db :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add (TmJPoly.smul 4 hS)
      (TmJPoly.smul 2 hL)) (TmJPoly.const 9)) _)
  have hM : TmJPoly fun W => Kl * (4 * (mkGroupK * ((W + 2) * (tmJPrepAK (2 * W + 7) + 1)) ^ 3) +
      7) ^ Dl :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 4 hS) (TmJPoly.const 7)) _)
  unfold tmJPrepK
  exact TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add
    (TmJPoly.add (TmJPoly.add hW hA) (TmJPoly.smul 2 hS)) hL) hT) hB) hM) (TmJPoly.const 100))

/-- The rows of a list of coordinate vectors as a matrix. -/
def tmJRowsMat {G t : ℕ} (zs : List (Fin t → ℤ)) (h : zs.length = G) : Matrix (Fin G) (Fin t) ℤ :=
  fun i => zs.get ⟨i, h ▸ i.2⟩

theorem tmJ_rowsMat_enc {G t : ℕ} (zs : List (Fin t → ℤ)) (h : zs.length = G) :
    encIntMatrix (tmJRowsMat zs h) = .list (zs.map linVecVal) := by
  subst h
  unfold encIntMatrix tmJRowsMat
  conv_rhs => rw [← List.map_get_finRange zs]
  simp only [List.map_map, Function.comp_def, linVecVal]

private theorem tmJP_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- **The context of the per-label program.** -/
theorem tmJ_prep_spec (ho : GroupOrder) (hcm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {f pa mk lg tl bt lac jo jm : ℕ},
      TmJPrepAt P f pa mk lg tl bt lac jo jm →
      P.prims[jo]? = some (groupOrderPrim ho) → P.prims[jm]? = some (linMembershipPrim hcm) →
      ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {sv : Val},
      Canon e c sv S → ∀ {m q : ℕ} (E : Fin m × Fin q ≃ S.dom),
      (domFin e S.dom).length = m * q → 0 < q →
      ∀ (σH σN σS : List (Equiv.Perm (Fin m))), gens σS ≤ gens σN →
      (∀ x ∈ gens σN, ∀ y ∈ gens σN, x * y * x⁻¹ * y⁻¹ ∈ gens σS) →
      ∀ [((gens σS).subgroupOf (gens σN)).Normal]
        [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))]
        (O : Fin q → Fin q → Option (Equiv.Perm (Fin m) × List (Equiv.Perm (Fin m)))),
      (∀ a, ∃ r gs, O a a = some (r, gs)) →
      ∀ (us : List Val), (∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) →
      (∀ p ∈ tmJLgList O, p.2 ∈ gens σN) →
      ∀ (vs : List Val) (lv rl : Val),
      FunAll P f (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl], .list us,
          .list vs])
        (fun out cost => (∃ (gs : List (Equiv.Perm (Fin k)))
            (Bm : Matrix (Fin (tmJLgList O).length) (Fin σN.length) ℤ)
            (M : Matrix (Fin σN.length) (Fin σN.length) ℤ),
            gens gs = groupFin e S.G ∧
            (∀ k', tmJHF σS σN (Bm k') = Additive.ofMul (QuotientGroup.mk'
              ((gens σS).subgroupOf (gens σN))
              (linIntoSubgroup (gens σN) ((tmJLgList O).get k').2))) ∧
            linPresentationCertificate M (tmJHF σS σN) ∧
            out = tmJHCtx (tmJGList e S E gs)
              ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))
              vs σS σN (tmJLgList O) (tmJTlList O) Bm M) ∧
          cost ≤ K * ((Val.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl],
            .list us, .list vs]).wt + 1) ^ D) := by
  obtain ⟨Kb, Db, hBt⟩ := tmJ_beta_spec hcm
  obtain ⟨Kl, Dl, hLac⟩ := linAbelianCoordinates_spec_poly ho hcm
  obtain ⟨K, D, hKD⟩ := tmJPrepK_poly Kb Db Kl Dl
  refine ⟨K, D, ?_⟩
  intro P f pa mk lg tl bt lac jo jm hA hjo hjm Ω C k e c S sv hsv m q E hs hq σH σN σS hle hc
    _ _ O hloc us hus hlgN vs lv rl
  obtain ⟨tab, gg, rg, nq, hPA⟩ := hA.hpa
  obtain ⟨rg1, tbR, row, mp, e1, fl, app, hLg⟩ := hA.hlg
  obtain ⟨rg2, tbE, e2, fl2, app2, hTl⟩ := hA.htl
  obtain ⟨mpb, eb, vv, hbf, hbmp, hbe, hbvv⟩ := hA.hbt
  obtain ⟨gs, hgs, dPA⟩ := tmJ_prepA_spec hPA e c hsv E hs hq σN
  refine FunAll.intro hA.hf ?_
  unfold tmJPrepF
  -- the input and its weight
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl],
      .list us, .list vs]).wt = W := ⟨_, rfl⟩
  have wc0 : (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]).wt < W :=
    hW ▸ wt_le_wt_list (by simp)
  have wus : (Val.list us).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wvs : (Val.list vs).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wsum := sum_wt_lt_wt_list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wsum
  have wN : (Val.list (σN.map encPerm)).wt < (a18Out σH σN σS 0).wt :=
    wt_le_wt_list (by simp)
  have wS : (Val.list (σS.map encPerm)).wt < (a18Out σH σN σS 0).wt :=
    wt_le_wt_list (by simp)
  have lN : σN.length < (Val.list (σN.map encPerm)).wt := by
    have := length_lt_wt_list (σN.map encPerm); simpa using this
  have lS : σS.length < (Val.list (σS.map encPerm)).wt := by
    have := length_lt_wt_list (σS.map encPerm); simpa using this
  -- the bounds
  obtain ⟨Ba, hBa⟩ : ∃ Ba, tmJPrepAK (2 * W + 7) = Ba := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs, mkGroupK * ((W + 2) * (Ba + 1)) ^ 3 = Bs := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl, tmJLgK (W + (Ba + 1) ^ 2) = Bl := ⟨_, rfl⟩
  obtain ⟨Bt, hBt'⟩ : ∃ Bt, tmJTlK (W + (Ba + 1) ^ 2) = Bt := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb, Kb * (4 * Bs + 2 * Bl + 9) ^ Db = Bb := ⟨_, rfl⟩
  obtain ⟨BM, hBM⟩ : ∃ BM, Kl * (4 * Bs + 7) ^ Dl = BM := ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb, W + Ba + 2 * Bs + Bl + Bt + Bb + BM + 100 = Sb := ⟨_, rfl⟩
  have hK : tmJPrepK Kb Db Kl Dl W = 10 ^ 6 * Sb := by
    unfold tmJPrepK; rw [← hSb, ← hBM, ← hBb, ← hBt', ← hBl, ← hBs, ← hBa]
  have hfin : 10 ^ 6 * Sb ≤ K * (W + 1) ^ D := hK ▸ hKD W
  -- step 1: the groups `G|_dom`, `N^q` and the local context
  set c0 := Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl] with hc0
  set V := Val.list [c0, .list us, .list vs] with hV
  set aV := Val.list [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), tmJLocCtx m q] with haV
  have hW2 : (Val.list [c0, Val.list us, Val.list vs]).wt = W := hW
  have r0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs]) (rest := []) (j := 0) (v := c0) rfl
  have r1 := Det.get' r0 (Det.nat 0) (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl])
    (v := sv) rfl
  have r2 := Det.get' r0 (Det.nat 2) (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl])
    (v := coordsVal e S E) rfl
  have r3 := Det.get' (Det.get' r0 (Det.nat 3)
    (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]) (v := a18Out σH σN σS 0) rfl)
    (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
      .nat 0]) (v := .list (σN.map encPerm)) rfl
  have wPA : (Val.list [sv, coordsVal e S E, .list (σN.map encPerm)]).wt ≤ 2 * W + 7 := by
    have := wt_list3_le sv (coordsVal e S E) (.list (σN.map encPerm)); omega
  have hPAc : tmJPrepAK (Val.list [sv, coordsVal e S E, .list (σN.map encPerm)]).wt ≤ Ba :=
    hBa ▸ tmJPrepAK_mono wPA
  have waV : aV.wt < Ba := by have := FunDet.wt_lt dPA; omega
  have hlcw : (tmJLocCtx m q).wt < aV.wt := wt_le_wt_list (by simp)
  have hm1 : m < (tmJLocCtx m q).wt :=
    (tmJP_lt_wt (1 : Equiv.Perm (Fin m))).trans (wt_le_wt_list (by simp))
  have hq1 : q < (tmJLocCtx m q).wt :=
    (tmJP_lt_wt (1 : Equiv.Perm (Fin q))).trans (wt_le_wt_list (by simp))
  have hmA : m < aV.wt := by omega
  have hqA : q < aV.wt := by omega
  have c1 := (Det.call (Det.mk3 r1 r2 r3) dPA).mono (c' := 20 * Sb) (by omega)
  refine (tmJ_letDet (C := 50000 * Sb) c1 ?_).mono fun u cu hu => ⟨hu.1, hu.2.trans (by
    rw [hW]; omega)⟩
  -- reads of the context `aV`
  have hlcE : tmJLocCtx m q = .list [encPerm (1 : Equiv.Perm (Fin m)),
      encPerm (1 : Equiv.Perm (Fin q)), .nat q, .nat m] := rfl
  have hle1 : σS.length + 2 ≤ W + 2 := by omega
  have hle2 : m + 1 ≤ Ba + 1 := by omega
  have hle3 : (m + 1) * (q + 1) ≤ (Ba + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  -- step 2: `N*`
  have dS := mkGroup_spec hA.hmk σS
  have wSv : (encGroup σS).wt < Bs := by
    have h := FunDet.wt_lt dS
    have : mkGroupK * ((σS.length + 2) * (m + 1)) ^ 3 ≤ Bs := by
      rw [← hBs]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul hle1 hle2) 3)
    omega
  have dN := mkGroup_spec hA.hmk σN
  have wNv : (encGroup σN).wt < Bs := by
    have h := FunDet.wt_lt dN
    have : mkGroupK * ((σN.length + 2) * (m + 1)) ^ 3 ≤ Bs := by
      rw [← hBs]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) hle2) 3)
    omega
  have s1 := Det.var' (P := P) (env := [V] ++ [aV]) (i := 1) (v := aV) rfl
  have s2 := Det.get' s1 (Det.nat 2) (vs := [encGroup (tmJGList e S E gs), encGroup
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
    tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  rw [hlcE] at s2
  have s3 := Det.get' s2 (Det.nat 3) (v := .nat m) rfl
  have t0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs]) (rest := [aV]) (j := 0) (v := c0) rfl
  have t3 := Det.get' (Det.get' t0 (Det.nat 3)
    (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]) (v := a18Out σH σN σS 0) rfl)
    (Det.nat 2) (vs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
      .nat 0]) (v := .list (σS.map encPerm)) rfl
  have hc2 := (Det.call (Det.mk2 s3 t3) dS).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.nat m) (Val.list (σS.map encPerm))
    have := wt_nat_le m
    have : mkGroupK * ((σS.length + 2) * (m + 1)) ^ 3 ≤ Bs := by
      rw [← hBs]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul hle1 hle2) 3)
    rw [hlcE] at hlcw
    have := wt_list4_le (encPerm (1 : Equiv.Perm (Fin m))) (encPerm (1 : Equiv.Perm (Fin q)))
      (.nat q) (.nat m)
    omega)
  refine (tmJ_letDet (C := 22300 * Sb) hc2 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 3: `N`
  have u1 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS]) (i := 1) (v := aV) rfl
  have u2 := Det.get' u1 (Det.nat 2) (vs := [encGroup (tmJGList e S E gs), encGroup
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
    tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  rw [hlcE] at u2
  have u3 := Det.get' u2 (Det.nat 3) (v := .nat m) rfl
  have u0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs]) (rest := [aV, encGroup σS])
    (j := 0) (v := c0) rfl
  have u4 := Det.get' (Det.get' u0 (Det.nat 3)
    (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]) (v := a18Out σH σN σS 0) rfl)
    (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
      .nat 0]) (v := .list (σN.map encPerm)) rfl
  have hc3 := (Det.call (Det.mk2 u3 u4) dN).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.nat m) (Val.list (σN.map encPerm))
    have := wt_nat_le m
    have : mkGroupK * ((σN.length + 2) * (m + 1)) ^ 3 ≤ Bs := by
      rw [← hBs]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) hle2) 3)
    rw [hlcE] at hlcw
    have := wt_list4_le (encPerm (1 : Equiv.Perm (Fin m))) (encPerm (1 : Equiv.Perm (Fin q)))
      (.nat q) (.nat m)
    omega)
  refine (tmJ_letDet (C := 11100 * Sb) hc3 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 4: the pairs `lg`
  have dL := tmJ_lg_spec hLg O hloc us hus
  have wLv : (tmJLgVal (tmJLgList O)).wt < Bl := by
    have h := FunDet.wt_lt dL
    have : tmJLgK ((Val.list us).wt + (m + 1) * (q + 1)) ≤ Bl := by
      rw [← hBl]; unfold tmJLgK; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  have v1 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN]) (i := 1)
    (v := aV) rfl
  have v2 := Det.get' v1 (Det.nat 2) (vs := [encGroup (tmJGList e S E gs), encGroup
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
    tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  rw [hlcE] at v2
  have v3 := Det.get' v2 (Det.nat 2) (v := .nat q) rfl
  have v0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs])
    (rest := [aV, encGroup σS, encGroup σN]) (j := 1) (v := .list us) rfl
  have hc4 := (Det.call (Det.mk2 v0 v3) dL).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.list us) (Val.nat q)
    have := wt_nat_le q
    have : tmJLgK ((Val.list us).wt + (m + 1) * (q + 1)) ≤ Bl := by
      rw [← hBl]; unfold tmJLgK; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    rw [hlcE] at hlcw
    have := wt_list4_le (encPerm (1 : Equiv.Perm (Fin m))) (encPerm (1 : Equiv.Perm (Fin q)))
      (.nat q) (.nat m)
    omega)
  refine (tmJ_letDet (C := 5500 * Sb) hc4 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 5: the triples `Tl`
  have dT := tmJ_tl_spec hTl O us hus
  have wTv : (tmJTlVal (tmJTlList O)).wt < Bt := by
    have h := FunDet.wt_lt dT
    have : tmJTlK ((Val.list us).wt + (m + 1) * (q + 1)) ≤ Bt := by
      rw [← hBt']; unfold tmJTlK; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  have x1 := Det.var' (P := P)
    (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++ [tmJLgVal (tmJLgList O)]) (i := 1)
    (v := aV) rfl
  have x2 := Det.get' x1 (Det.nat 2) (vs := [encGroup (tmJGList e S E gs), encGroup
    ((tmJNqList (q := q) σN).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
    tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  rw [hlcE] at x2
  have x3 := Det.get' x2 (Det.nat 2) (v := .nat q) rfl
  have x0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs])
    (rest := [aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O)]) (j := 1) (v := .list us) rfl
  have hc5 := (Det.call (Det.mk2 x0 x3) dT).mono (c' := 20 * Sb) (by
    have := wt_list2_le (Val.list us) (Val.nat q)
    have := wt_nat_le q
    have : tmJTlK ((Val.list us).wt + (m + 1) * (q + 1)) ≤ Bt := by
      rw [← hBt']; unfold tmJTlK; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    rw [hlcE] at hlcw
    have := wt_list4_le (encPerm (1 : Equiv.Perm (Fin m))) (encPerm (1 : Equiv.Perm (Fin q)))
      (.nat q) (.nat m)
    omega)
  refine (tmJ_letDet (C := 2700 * Sb) hc5 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 6: the coordinate vectors of the stored local generators
  have dB := hBt hbf hbmp hbe hbvv hjm σS σN hle (tmJLgList O) hlgN
  have wBin : (Val.list [encGroup σS, encGroup σN, tmJLgVal (tmJLgList O)]).wt + 1 ≤
      4 * Bs + 2 * Bl + 9 := by
    have := wt_list3_le (encGroup σS) (encGroup σN) (tmJLgVal (tmJLgList O)); omega
  have dB' := dB.mono (Q' := fun w c => (∃ zs : List (Fin σN.length → ℤ),
      w = .list (zs.map linVecVal) ∧
      List.Forall₂ (fun u z => Additive.ofMul (QuotientGroup.mk' ((gens σS).subgroupOf (gens σN))
        (linIntoSubgroup (gens σN) u)) = tmJHF σS σN z) ((tmJLgList O).map Prod.snd) zs) ∧
      c ≤ Bb) fun w c h => ⟨h.1, h.2.trans (by
        rw [← hBb]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wBin _))⟩
  have y2 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
    [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)]) (i := 2) (v := encGroup σS) rfl
  have y3 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
    [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)]) (i := 3) (v := encGroup σN) rfl
  have y4 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
    [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)]) (i := 4) (v := tmJLgVal (tmJLgList O))
    rfl
  have y5 := (Det.mk3 y2 y3 y4).mono (c' := 20 * Sb) (by
    have := wt_list3_le (encGroup σS) (encGroup σN) (tmJLgVal (tmJLgList O)); omega)
  refine (tmJ_letCall (C := 830 * Sb) y5 dB' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro bV ⟨zs, rfl, hzs⟩ wbV
  have hzl : zs.length = (tmJLgList O).length := by
    rw [← List.Forall₂.length_eq hzs, List.length_map]
  set Bm := tmJRowsMat zs hzl with hBmD
  have hBm : ∀ k', tmJHF σS σN (Bm k') = Additive.ofMul (QuotientGroup.mk'
      ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) ((tmJLgList O).get k').2)) := by
    intro k'
    obtain ⟨-, hg⟩ := List.forall₂_iff_get.1 hzs
    have := hg k' (by simp) (by rw [hzl]; exact k'.2)
    simp only [List.get_eq_getElem, List.getElem_map] at this
    rw [hBmD, tmJRowsMat, List.get_eq_getElem, ← this, List.get_eq_getElem]
  -- step 7: the presentation matrix of `N / N*`
  have dM := hLac hA.hlac hjo hjm σS σN hle hc
  have wMin : (Val.list [encGroup σS, encGroup σN]).wt + 1 ≤ 4 * Bs + 7 := by
    have := wt_list2_le (encGroup σS) (encGroup σN); omega
  have dM' := dM.mono (Q' := fun w c => (∃ M : Matrix (Fin σN.length) (Fin σN.length) ℤ,
      w = encIntMatrix M ∧ linPermPresentation σS σN M) ∧ c ≤ BM) fun w c h => ⟨h.1, h.2.trans (by
        rw [← hBM]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wMin _))⟩
  have z2 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
    [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)] ++ [.list (zs.map linVecVal)]) (i := 2)
    (v := encGroup σS) rfl
  have z3 := Det.var' (P := P) (env := [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
    [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)] ++ [.list (zs.map linVecVal)]) (i := 3)
    (v := encGroup σN) rfl
  have z5 := (Det.mk2 z2 z3).mono (c' := 20 * Sb) (by
    have := wt_list2_le (encGroup σS) (encGroup σN); omega)
  refine (tmJ_letCall (C := 400 * Sb) z5 dM' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro MV ⟨M, rfl, hMp⟩ wMV
  have hM : linPresentationCertificate M (tmJHF σS σN) := by
    obtain ⟨_, _, h⟩ := hMp
    exact h
  -- the body: the eleven entries of the context
  have hBmE : encIntMatrix Bm = .list (zs.map linVecVal) := tmJ_rowsMat_enc zs hzl
  obtain ⟨E8, hE8⟩ : ∃ E8 : List Val, [V] ++ [aV] ++ [encGroup σS] ++ [encGroup σN] ++
      [tmJLgVal (tmJLgList O)] ++ [tmJTlVal (tmJTlList O)] ++ [.list (zs.map linVecVal)] ++
      [encIntMatrix M] = E8 := ⟨_, rfl⟩
  rw [hE8]
  have hE8' : E8 = [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M] := hE8.symm
  subst hE8'
  have g1 := Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 1) (v := aV) rfl
  have hav : aV = .list [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), tmJLocCtx m q] := haV
  rw [hav] at g1
  have hgG : (encGroup (tmJGList e S E gs)).wt < aV.wt := wt_le_wt_list (by simp)
  have hgN : (encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))).wt < aV.wt :=
    wt_le_wt_list (by simp)
  have hav2 : (Val.list [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), tmJLocCtx m q]).wt = aV.wt := by
    rw [haV]
  have e0 := (Det.get' g1 (Det.nat 2) (v := tmJLocCtx m q) rfl).mono (c' := 20 * Sb) (by omega)
  have e10 := (Det.get' g1 (Det.nat 0) (v := encGroup (tmJGList e S E gs)) rfl).mono
    (c' := 20 * Sb) (by omega)
  have e9 := (Det.get' g1 (Det.nat 1) (v := encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))))) rfl).mono
    (c' := 20 * Sb) (by omega)
  have e1 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 7)
      (v := encIntMatrix M) rfl).mono (c' := 20 * Sb) (by omega)
  have e2 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 6)
      (v := .list (zs.map linVecVal)) rfl).mono (c' := 20 * Sb) (by omega)
  have e3 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 5)
      (v := tmJTlVal (tmJTlList O)) rfl).mono (c' := 20 * Sb) (by omega)
  have e4 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 4)
      (v := tmJLgVal (tmJLgList O)) rfl).mono (c' := 20 * Sb) (by omega)
  have e5 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 3)
      (v := encGroup σN) rfl).mono (c' := 20 * Sb) (by omega)
  have e6 := (Det.var' (P := P) (env := [V, aV, encGroup σS, encGroup σN, tmJLgVal (tmJLgList O),
      tmJTlVal (tmJTlList O), .list (zs.map linVecVal), encIntMatrix M]) (i := 2)
      (v := encGroup σS) rfl).mono (c' := 20 * Sb) (by omega)
  have a0 := Det.arg' (P := P) (vs := [c0, .list us, .list vs]) (rest := [aV, encGroup σS,
    encGroup σN, tmJLgVal (tmJLgList O), tmJTlVal (tmJTlList O), .list (zs.map linVecVal),
    encIntMatrix M]) (j := 0) (v := c0) rfl
  have e7 := (Det.get' (Det.get' a0 (Det.nat 3)
    (vs := [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rl]) (v := a18Out σH σN σS 0) rfl)
    (Det.nat 1) (vs := [.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm),
      .nat 0]) (v := .list (σN.map encPerm)) rfl).mono (c' := 20 * Sb) (by omega)
  have e8 := (Det.arg' (P := P) (vs := [c0, .list us, .list vs]) (rest := [aV, encGroup σS,
    encGroup σN, tmJLgVal (tmJLgList O), tmJTlVal (tmJTlList O), .list (zs.map linVecVal),
    encIntMatrix M]) (j := 2) (v := .list vs) rfl).mono (c' := 20 * Sb) (by omega)
  have hout : (Val.list [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), .list vs, .list (σN.map encPerm),
      encGroup σS, encGroup σN, tmJLgVal (tmJLgList O), tmJTlVal (tmJTlList O),
      .list (zs.map linVecVal), encIntMatrix M, tmJLocCtx m q]).wt ≤ 7 * Sb := by
    have := wt_list_le [encGroup (tmJGList e S E gs), encGroup ((tmJNqList (q := q) σN).map
      (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))), .list vs, .list (σN.map encPerm),
      encGroup σS, encGroup σN, tmJLgVal (tmJLgList O), tmJTlVal (tmJTlList O),
      .list (zs.map linVecVal), encIntMatrix M, tmJLocCtx m q]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have hmk := tmJ_mkR_det (P := P) (c := 20 * Sb) (Wb := 7 * Sb)
    [.get (.var 1) (.nat 2), .var 7, .var 6, .var 5, .var 4, .var 3, .var 2,
      .get (.get (arg 0) (.nat 3)) (.nat 1), arg 2, .get (.var 1) (.nat 1), .get (.var 1) (.nat 0)]
    [tmJLocCtx m q, encIntMatrix M, .list (zs.map linVecVal), tmJTlVal (tmJTlList O),
      tmJLgVal (tmJLgList O), encGroup σN, encGroup σS, .list (σN.map encPerm), .list vs,
      encGroup ((tmJNqList (q := q) σN).map
        (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)))),
      encGroup (tmJGList e S E gs)]
    (by
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
      exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩)
    (by simpa using hout)
  refine EvalAll.mono hmk fun u cu hu => ⟨⟨gs, Bm, M, hgs, hBm, hM, ?_⟩, ?_⟩
  · rw [hu.1, tmJHCtx, hBmE]
    rfl
  · have := hu.2
    simp only [List.length_cons, List.length_nil] at this
    omega

end GI.Impl
