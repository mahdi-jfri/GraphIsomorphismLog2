module

public import Workspace.Degree.ResetProg
public import Workspace.Degree.RootState

@[expose] public section

/-!
# The root program

`rootFreshBody` runs the fresh phase of the root: it calls `prepF` of the general algorithm, clamps
the cap of the one interval of the fresh hierarchy to `D` (`clampE`), calls `cont` on the value of
the root state, and lifts the answer. It is `resetBody` with a different second step. The number `D`
enters as the expression `dE`, which is `.nat D` in the program for one `D`.

`rootTopBody` calls the general solver `fs` when `k ≤ N₀` or `k ≤ D`, and the fresh phase otherwise.

`rootFresh_spec`: every evaluation returns a canonical answer of `S`, at the cost of the call of
`cont` and a polynomial in the weight of the input and `D`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab Preimage NormalizedFactor)

variable {Ω C : Type} {k : ℕ}

/-- The clamp of the fresh hierarchy value `h`: `[]` stays, and `[[lab, M, M, 0]]` becomes
`[[lab, M, min M D, 0]]`. -/
def clampE (h dE : Expr) : Expr :=
  .ite (.length h)
    (mk1 (mk4 (.get (.get h (.nat 0)) (.nat 0)) (.get (.get h (.nat 0)) (.nat 1))
      (minE (.get (.get h (.nat 0)) (.nat 2)) dE) (.nat 0)))
    h

theorem Det.clampE {P : Program} {env : List Val} {h dE : Expr} {labv : Val} {M D ch cd : ℕ}
    (hh : Det P env h (fhierVal labv M) ch) (hd : Det P env dE (.nat D) cd) :
    Det P env (clampE h dE) (clampHierVal labv M D)
      (100 * (ch + cd + (fhierVal labv M).wt + D + 20)) := by
  have hW := wt_fhierVal_le labv M
  unfold GI.Degree.clampE
  by_cases h1 : M = 1
  · have e1 : fhierVal labv M = .list [] := by simp [fhierVal, h1]
    have e2 : clampHierVal labv M D = .list [] := by simp [clampHierVal, h1]
    rw [e1] at hh ⊢
    rw [e2]
    have := Det.ite_zero (t := mk1 (mk4 (.get (.get h (.nat 0)) (.nat 0))
      (.get (.get h (.nat 0)) (.nat 1)) (minE (.get (.get h (.nat 0)) (.nat 2)) dE) (.nat 0)))
      (Det.length hh) hh
    refine this.mono ?_
    simp only [List.length_nil, wt_list_nil]
    omega
  · have e1 : fhierVal labv M = hierVal labv M := by simp [fhierVal, h1]
    have e2 : clampHierVal labv M D = .list [.list [labv, .nat M, .nat (min M D), .nat 0]] := by
      simp [clampHierVal, h1]
    rw [e1] at hh hW ⊢
    rw [e2]
    set I := Val.list [labv, .nat M, .nat M, .nat 0]
    have hI : I.wt < (hierVal labv M).wt := wt_le_wt_list (by simp [hierVal, I])
    have hl : labv.wt < I.wt := wt_le_wt_list (by simp [I])
    have hm : (Val.nat M).wt < I.wt := wt_le_wt_list (by simp [I])
    have g0 := Det.get' hh (Det.nat 0) (vs := [I]) rfl
    have g1 := Det.get' g0 (Det.nat 0) (vs := [labv, .nat M, .nat M, .nat 0]) rfl
    have g2 := Det.get' g0 (Det.nat 1) (vs := [labv, .nat M, .nat M, .nat 0]) (v := .nat M) rfl
    have g3 := Det.get' g0 (Det.nat 2) (vs := [labv, .nat M, .nat M, .nat 0]) (v := .nat M) rfl
    have gm := Det.minE g3 hd
    have g4 := Det.mk1 (Det.mk4 g1 g2 gm (Det.nat 0) (P := P) (env := env))
    have hc := Det.length hh
    have := Det.ite_pos (e := h) hc (by simp [hierVal]) g4
    refine this.mono ?_
    have w1 := Lang.wt_list4_le labv (.nat M) (.nat (min M D)) (.nat 0)
    have w2 := wt_list1_le (Val.list [labv, .nat M, .nat (min M D), .nat 0])
    have w3 : (Val.nat (min M D)).wt ≤ (Val.nat M).wt := wt_nat_mono (min_le_left _ _)
    have w4 : (Val.nat D).wt ≤ D + 2 := wt_nat_le D
    have w5 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    simp only [List.length_cons, List.length_nil]
    omega

/-- The body of the fresh phase of the root on a state value `v`. -/
def rootFreshBody (prep cont lift : ℕ) (dE : Expr) : Expr :=
  .letE (.call prep (.var 0))
  (.letE (clampE (.get (.get (.var 1) (.nat 3)) (.nat 5)) dE)
  (.letE (Expr.mkList [.get (.get (.var 1) (.nat 3)) (.nat 0), .get (.get (.var 1) (.nat 3)) (.nat 1),
      .get (.get (.var 1) (.nat 3)) (.nat 2), .get (.get (.var 1) (.nat 3)) (.nat 3),
      .get (.get (.var 1) (.nat 3)) (.nat 4), .var 2, .get (.get (.var 1) (.nat 3)) (.nat 6),
      .get (.get (.var 1) (.nat 3)) (.nat 7), .get (.get (.var 1) (.nat 3)) (.nat 8),
      .get (.get (.var 1) (.nat 3)) (.nat 9)])
  (.letE (.call cont (.var 3))
    (.call lift (mk2 (mk4 (arg 0) (.get (.var 1) (.nat 2)) (.get (.var 1) (.nat 1))
      (.get (.var 1) (.nat 0))) (.var 4))))))

/-- The cost of the fresh phase of the root besides the call of `cont`, in `X = wt v + 1`. -/
def rootOwn (pst pp pf : Prim) (X D : ℕ) : ℕ :=
  prepCost pst X + liftCost pp pf X + 10 ^ 4 * (resetY X + D + 100)

/-- **The fresh phase of the root.** -/
theorem rootFresh_spec (hst : PointwiseStab) (hpre : Preimage) (hfac : NormalizedFactor)
    {P : Program} {f prep red dom col hier ap rep lo cnt ob jst lift jpre jfac trans : ℕ} {dE : Expr}
    {D : ℕ} (hb : P.funs[f]? = some (rootFreshBody prep trans lift dE))
    (hdE : ∀ env, Det P env dE (.nat D) (D + 3))
    (hp : PrepAt P prep red dom col hier ap rep lo cnt ob jst)
    (hjs : P.prims[jst]? = some (pointwiseStabPrim hst))
    (hl : LiftAt P lift dom jpre jfac) (hjp : P.prims[jpre]? = some (preimagePrim hpre))
    (hjf : P.prims[jfac]? = some (normalizedFactorPrim hfac))
    (e : Ω ≃ Fin k) (c : C → ℕ) (T : State Ω C) {v : Val} (hsv : StateVal e c v T)
    (h0 : 0 < T.size) {b : ℝ}
    (htr : ∀ a : T.dom, (∀ b, Nat.card (orb T.domGroup b) ≤ Nat.card (orb T.domGroup a)) →
      ∀ val, Canon (domEquiv e T.dom) (freshCode e c T) val (rootState T D a) →
      FunAll P trans val (fun u cu => AnsC (domEquiv e T.dom) u (rootState T D a).answer ∧
        (cu : ℝ) ≤ b)) :
    FunAll P f v (fun w cost => AnsC e w T.answer ∧ (cost : ℝ) ≤
      b + rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac)
        (v.wt + 1) D) := by
  have hkv := StateVal.k_le_wt hsv
  obtain ⟨gv, dv, xv, yv, hvIn, rv, -, -, -, -, -, -, hveq⟩ := id hsv
  set s := (domFin e T.dom).length with hsd
  have hsT : T.size = s := card_dom_eq e T.dom
  have hsk : s ≤ k := length_domFin_le
  set X := v.wt + 1 with hX
  set Y := resetY X with hY
  have hkX : k + 1 ≤ X := by omega
  have hYX : 10 ^ 6 * (X + 2) ^ 6 = Y := rfl
  refine FunAll.intro hb ?_
  have d0 := Det.var' (P := P) (env := [v]) (i := 0) rfl
  refine EvalAll.letE (EvalAll.call_spec d0 (prep_spec hst hp hjs e c T h0 hsv)) ?_
  rintro w1 c1 ⟨cb1, ⟨⟨gs₀, hsF, labF, a, hgs₀, hl₀, hmax, hcan0, rfl, hw1⟩, hcb1⟩, hc1⟩
  set cx := natList (cmpCodes e c T T.x)
  set cy := natList (cmpCodes e c T T.y)
  set gF := encGroup hsF
  set hF := fhierVal (encFun labF) (Nat.card (orb T.domGroup a))
  have hcanR := canon_root T D a hcan0
  set hsV := clampHierVal (encFun labF) (Nat.card (orb T.domGroup a)) D with hhsV
  set v' := freshVal s gF cx cy hsV with hv'
  set v0 := freshVal s gF cx cy hF with hv0
  set w1 := Val.list [encGroup gs₀, domCtx e T.dom, .nat s, v0] with hw1d
  have hP6 : X + 2 ≤ (X + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hk6 : (k + 1) ^ 6 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hs6 : (s + 2) ^ 6 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hkk : k * (2 * k + 5) + 4 ≤ 10 * (X + 2) ^ 6 := by
    have h1 : (X + 2) ^ 2 ≤ (X + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : k * (2 * k + 5) ≤ (X + 2) * (3 * (X + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hv'w : v'.wt ≤ 10 ^ 4 * (s + 2) ^ 6 := by
    have := hcanR.wt_le_poly
    have hN : (rootState T D a).N = s := hsT
    rwa [hN] at this
  have hhw : hsV.wt < v'.wt := wt_le_wt_list (by simp [hv', freshVal])
  have hctx1 : (domCtx e T.dom).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hsw1 : (Val.nat s).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have h0w1 : v0.wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hFw : hF.wt < v0.wt := wt_le_wt_list (by simp [hv0, freshVal])
  have g1 := Det.var' (P := P) (env := [v, w1]) (i := 1) rfl
  have gv0' := Det.get' g1 (Det.nat 3) (v := v0)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have gh5 := Det.get' gv0' (Det.nat 5) (v := hF) (vs := [Val.nat s, gF,
    .list (List.replicate s (.nat 1)), cx, cy, hF, .list [], .nat 0, .nat 2, .nat s]) rfl
  have d2 := Det.clampE gh5 (hdE [v, w1])
  refine EvalAll.letE d2 ?_
  rintro _ c2 ⟨rfl, hc2⟩
  have g1' := Det.var' (P := P) (env := [v, w1, hsV]) (i := 1) rfl
  have gv0 := Det.get' g1' (Det.nat 3) (v := v0)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have gf : ∀ (i : ℕ) (u : Val), [Val.nat s, gF, .list (List.replicate s (.nat 1)), cx, cy, hF,
      .list [], .nat 0, .nat 2, .nat s][i]? = some u →
      Det P [v, w1, hsV] (.get (.get (.var 1) (.nat 3)) (.nat i)) u (3 * Y + 40) := by
    intro i u h
    have hi10 : i < 10 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simpa using hc)] at h
      cases h
    have hu : u.wt < v0.wt := wt_le_wt_list (List.mem_of_getElem? h)
    refine (Det.get' gv0 (Det.nat i) (vs := [Val.nat s, gF, .list (List.replicate s (.nat 1)), cx,
      cy, hF, .list [], .nat 0, .nat 2, .nat s]) h).mono ?_
    omega
  have gh : Det P [v, w1, hsV] (.var 2) hsV (3 * Y + 40) :=
    (Det.var' (P := P) (env := [v, w1, hsV]) (i := 2) rfl).mono (by omega)
  have d3 : Det P [v, w1, hsV] (Expr.mkList [.get (.get (.var 1) (.nat 3)) (.nat 0),
      .get (.get (.var 1) (.nat 3)) (.nat 1), .get (.get (.var 1) (.nat 3)) (.nat 2),
      .get (.get (.var 1) (.nat 3)) (.nat 3), .get (.get (.var 1) (.nat 3)) (.nat 4), .var 2,
      .get (.get (.var 1) (.nat 3)) (.nat 6), .get (.get (.var 1) (.nat 3)) (.nat 7),
      .get (.get (.var 1) (.nat 3)) (.nat 8), .get (.get (.var 1) (.nat 3)) (.nat 9)]) v'
      (10 * (3 * Y + 40 + v'.wt + 1) + 5) :=
    Det.mkList (c := 3 * Y + 40) [(.get (.get (.var 1) (.nat 3)) (.nat 0), .nat s),
      (.get (.get (.var 1) (.nat 3)) (.nat 1), gF),
      (.get (.get (.var 1) (.nat 3)) (.nat 2), .list (List.replicate s (.nat 1))),
      (.get (.get (.var 1) (.nat 3)) (.nat 3), cx), (.get (.get (.var 1) (.nat 3)) (.nat 4), cy),
      (.var 2, hsV), (.get (.get (.var 1) (.nat 3)) (.nat 6), .list []),
      (.get (.get (.var 1) (.nat 3)) (.nat 7), .nat 0),
      (.get (.get (.var 1) (.nat 3)) (.nat 8), .nat 2),
      (.get (.get (.var 1) (.nat 3)) (.nat 9), .nat s)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact gf 0 _ rfl
      · exact gf 1 _ rfl
      · exact gf 2 _ rfl
      · exact gf 3 _ rfl
      · exact gf 4 _ rfl
      · exact gh
      · exact gf 6 _ rfl
      · exact gf 7 _ rfl
      · exact gf 8 _ rfl
      · exact gf 9 _ rfl)
  refine EvalAll.letE d3 ?_
  rintro _ c3 ⟨rfl, hc3⟩
  refine EvalAll.letE (EvalAll.call_spec
    (Det.var' (P := P) (env := [v, w1, hsV, v']) (i := 3) rfl) (htr a hmax v' hcanR)) ?_
  rintro u' c4 ⟨cb4, ⟨hA', hcb4⟩, hc4⟩
  have hsub : (rootState T D a).answer ⊆ (restrictHom T.G T.dom T.dom_inv).range := by
    intro g hg
    exact hg.1
  have hlift := lift_spec hpre hfac hl hp.domAt hjp hjf e T hgs₀ hl₀ hA' hsub
  have q1 := Det.arg' (P := P) (vs := [.nat k, gv, dv, xv, yv, hvIn, rv,
      boolVal T.floor, .nat T.h, .nat T.N]) (rest := [w1, hsV, v', u']) (j := 0) rfl
  rw [← hveq] at q1
  have g1'' := Det.var' (P := P) (env := [v, w1, hsV, v', u']) (i := 1) rfl
  have q2 := Det.get' g1'' (Det.nat 2) (v := .nat s)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q3 := Det.get' g1'' (Det.nat 1) (v := domCtx e T.dom)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q4 := Det.get' g1'' (Det.nat 0) (v := encGroup gs₀)
    (vs := [encGroup gs₀, domCtx e T.dom, .nat s, v0]) rfl
  have q5 := Det.var' (P := P) (env := [v, w1, hsV, v', u']) (i := 4) rfl
  refine (EvalAll.call_spec (Det.mk2 (Det.mk4 q1 q2 q3 q4) q5) hlift).mono ?_
  rintro w c5 ⟨cb5, ⟨hAns, hcb5⟩, hc5⟩
  rw [liftAnswer_root] at hAns
  refine ⟨hAns, ?_⟩
  have wu := hA'.wt_le
  have wu' : ansW s ≤ 400 * (k + 1) ^ 6 :=
    (ansW_le_pow _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
  have ww := hAns.wt_le
  have ww' := ansW_le_pow k
  have wctx := wt_liftCtx_le e T.dom hl₀
  have wl2 := wt_list2_le (liftCtx e T.dom gs₀) u'
  have hlc := liftCost_mono (preimagePrim hpre) (normalizedFactorPrim hfac) (show k ≤ X by omega)
  have eL : (Val.list [Val.nat k, Val.nat s, domCtx e T.dom, encGroup gs₀]).wt =
      (liftCtx e T.dom gs₀).wt := rfl
  have eL2 : (Val.list [Val.list [Val.nat k, Val.nat s, domCtx e T.dom, encGroup gs₀], u']).wt =
      (Val.list [liftCtx e T.dom gs₀, u']).wt := rfl
  have hg0 : (encGroup gs₀).wt < w1.wt := wt_le_wt_list (by simp [hw1d])
  have hnat : c1 + (c2 + (c3 + (c4 + c5 + w.wt + 1) + w.wt + 1) + w.wt + 1) + w.wt + 1 ≤
      rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X D + cb4 := by
    unfold rootOwn
    rw [← hY]
    have a2 : ansW (domFin e T.dom).length = ansW s := rfl
    have a3 : prepCost (pointwiseStabPrim hst) (v.wt + 1) = prepCost (pointwiseStabPrim hst) X := rfl
    have a4 : (fhierVal (encFun labF) (Nat.card (orb T.domGroup a))).wt = hF.wt := rfl
    omega
  have hnat' : ((c1 + (c2 + (c3 + (c4 + c5 + w.wt + 1) + w.wt + 1) + w.wt + 1) + w.wt + 1 : ℕ) : ℝ) ≤
      ((rootOwn (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) X D : ℕ) : ℝ)
        + (cb4 : ℝ) := by exact_mod_cast hnat
  linarith

/-- **The root**: the general solver `fs` when `k ≤ N₀` or `k ≤ D`, the fresh phase `rf` otherwise. -/
def rootTopBody (fs rf N₀ : ℕ) (dE : Expr) : Expr :=
  .ite (.arith .lt (.nat N₀) (.get (.var 0) (.nat 0)))
    (.ite (.arith .lt dE (.get (.var 0) (.nat 0))) (.call rf (.var 0)) (.call fs (.var 0)))
    (.call fs (.var 0))

theorem rootTop_spec {Pg : Program} {f fs rf N₀ D : ℕ} {dE : Expr}
    (hf : Pg.funs[f]? = some (rootTopBody fs rf N₀ dE))
    (hdE : ∀ env, Det Pg env dE (.nat D) (D + 3)) {k : ℕ} {vs : List Val}
    (hk : vs[0]? = some (.nat k)) {Post : Val → ℕ → Prop}
    (h1 : N₀ < k → D < k → FunAll Pg rf (.list vs) Post)
    (h2 : ¬ (N₀ < k ∧ D < k) → FunAll Pg fs (.list vs) Post) :
    FunAll Pg f (.list vs) fun u cost => ∃ c₀, Post u c₀ ∧
      cost ≤ c₀ + 20 * ((Val.list vs).wt + N₀ + D + 20) + 3 * (u.wt + 1) := by
  have dk := Det.get' (Det.var' (P := Pg) (env := [.list vs]) (i := 0) rfl) (Det.nat 0) hk
  have wk : (Val.nat k).wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hk)
  have dt := Det.arith (op := .lt) (Det.nat N₀ (P := Pg) (env := [.list vs])) dk
  have hwlt : ∀ x y : ℕ, (Val.nat (Machine.BinOp.eval .lt x y)).wt ≤ 3 := by
    intro x y; simp only [Machine.BinOp.eval]; split <;> decide
  have h3 := hwlt N₀ k
  have dv := Det.var' (P := Pg) (env := [.list vs]) (i := 0) rfl
  refine FunAll.intro hf (EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y cc h => ?_)
  obtain ⟨hy, hcc⟩ := h
  injection hy with hy
  subst hy
  by_cases hN : N₀ < k
  · have e1 : Machine.BinOp.eval .lt N₀ k = 1 := by change (if _ then 1 else 0) = 1; rw [if_pos hN]
    rw [e1] at hcc h3 ⊢
    rw [if_neg one_ne_zero]
    have dt2 := Det.arith (op := .lt) (hdE [.list vs]) dk
    have h4 := hwlt D k
    refine EvalAll.ite dt2 (fun _ _ h => ⟨_, h.1⟩) fun y2 cc2 h => ?_
    obtain ⟨hy2, hcc2⟩ := h
    injection hy2 with hy2
    subst hy2
    by_cases hD : D < k
    · have e2 : Machine.BinOp.eval .lt D k = 1 := by change (if _ then 1 else 0) = 1; rw [if_pos hD]
      rw [e2] at hcc2 h4 ⊢
      rw [if_neg one_ne_zero]
      refine EvalAll.call_funAll dv fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      refine (h1 hN hD).mono fun u cost hP => ⟨cost, hP, ?_⟩
      omega
    · have e2 : Machine.BinOp.eval .lt D k = 0 := by change (if _ then 1 else 0) = 0; rw [if_neg hD]
      rw [e2] at hcc2 h4 ⊢
      rw [if_pos rfl]
      refine EvalAll.call_funAll dv fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      refine (h2 fun h => hD h.2).mono fun u cost hP => ⟨cost, hP, ?_⟩
      omega
  · have e1 : Machine.BinOp.eval .lt N₀ k = 0 := by change (if _ then 1 else 0) = 0; rw [if_neg hN]
    rw [e1] at hcc h3 ⊢
    rw [if_pos rfl]
    refine EvalAll.call_funAll dv fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (h2 fun h => hN h.1).mono fun u cost hP => ⟨cost, hP, ?_⟩
    omega

end GI.Degree
