module

public import Workspace.Degree.GraphCtx

/-!
# The graph program

`graphFuns b fd j`: decode the input, compute the largest degree `m` and `D = m + 6`, generators of
the automorphism group of `X` (Lemma 9.5 of the paper), an isomorphism from `X` to
`Y` if there is one (Lemma 9.6), and the output. This file proves that it is correct, with a cost
in terms of the cost `S` of the string solver.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- A `let` whose bound value comes from a call with a specification. -/
theorem giLetCall {P : Program} {env : List Val} {T : ℕ} {f : ℕ} {a body : Expr} {x : Val}
    {m K : ℕ} {Q : Val → ℕ → Prop} {R : Val → Prop} (ha : Lv P env T a x m) (hf : FunAll P f x Q)
    (hb : ∀ w c, Q w c → EvalAll P (env ++ [w]) body fun w' cb =>
      R w' ∧ m * T + c + w.wt + 1 + cb + w'.wt + 1 ≤ K) :
    EvalAll P env (.letE (.call f a) body) fun w cost => R w ∧ cost ≤ K :=
  .letE (Ra := fun w c => ∃ c0, Q w c0 ∧ c ≤ m * T + c0 + w.wt + 1)
    (EvalAll.call_funAll ha fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact hf.mono fun w cb hw => ⟨cb, hw, by omega⟩)
    fun v ca ⟨c0, hq, hc⟩ => (hb v c0 hq).mono fun w cb hw => ⟨hw.1, by omega⟩

/-- The body, on `[n, adj X, adj Y]` with `n > 0`. -/
def bodyE (rng deg ctx aut iso tab out : ℕ) : Expr :=
  .letE (.call rng (arg 0))
  (.letE (.call deg (mk3 (mk3 (arg 1) (arg 2) (.var 1)) (arg 0) (.nat 0)))
  (.letE (.call ctx (mk3 (.var 0) (.var 1) (.var 2)))
  (.letE (.call aut (mk3 (.get (.var 3) (.nat 0)) (.arith .mul (arg 0) (arg 0)) .nil))
  (.letE (.call iso (mk3 (.get (.var 3) (.nat 1)) (arg 0)
      (mk2 (.call tab (mk2 (arg 0) (.var 1))) (.nat 1))))
    (.ite (.get (.var 5) (.nat 1)) (.call out (mk2 (.get (.var 5) (.nat 0)) (.var 4)))
      (mk1 (.nat 0)))))))

/-- The cost of the table of the constant `n`. -/
def tbC (n : ℕ) : ℕ := n * (100 * WB n) + mapK * (n + 1) * (10 * WB n)

theorem tb_spec {P : Program} {t : ℕ} (hT : P.HasAt t (tabFuns t (arg 0))) :
    FunDet P t (.list [.nat n, ids n]) (encFun fun _ : Fin n => n) (tbC n) := by
  have h0 := WB_ge n
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wc : (encFun fun _ : Fin n => n).wt ≤ WB n := table_wt (by omega) fun _ => le_rfl
  have w2 : (Val.list [.nat n, ids n]).wt ≤ 2 * (2 * WB n + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)
  have := tabN_spec (T := 100 * WB n) (K := 1) (W := 10 * WB n) (c := .nat n)
    (f := fun _ : Fin n => n) hT (fun i => by
      have w3 : (Val.list [.nat n, .nat i]).wt ≤ 2 * (2 * WB n + 1) + 4 := wt_lit _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl)
        · omega
        · exact fin_wt (by omega) i)
      exact Lv.arg rfl (by omega)) (by omega)
  simpa [tbC] using this

/-- The budget of the body. -/
noncomputable def bodyT (h : Membership) (S n : ℕ) : ℕ :=
  rngC n + degLC n + 1000000000 * ctxT n + autLC h S n + isoLC h S n + 1000 * outT n + tbC n +
    1000 * AL n + 1000 * OW n + 1000 * WB n

/-- The bound of the body. -/
noncomputable def bodyC (h : Membership) (S n : ℕ) : ℕ := 1000000000 * bodyT h S n

/-- The functions of the body and the parts it calls. -/
structure BodyAt (P : Program) (r g c a i t o fd j : ℕ) : Prop where
  rng : P.HasAt r (rangeFuns r)
  deg : P.HasAt g (maxDegFuns g)
  ctx : P.funs[c]? = some (ctxE r)
  aut : P.HasAt a (autFuns a fd j)
  iso : P.HasAt i (isoFuns i fd j)
  tab : P.HasAt t (tabFuns t (arg 0))
  out : P.HasAt o (outFuns o)

set_option maxHeartbeats 8000000 in
/-- **The body.** -/
theorem body_spec {P : Program} {f rng deg ctx aut iso tab out fd j S d : ℕ} (h : Membership)
    (hM : P.funs[f]? = some (bodyE rng deg ctx aut iso tab out))
    (hB : BodyAt P rng deg ctx aut iso tab out fd j) (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : ∀ D, 6 ≤ D → D ≤ d + 6 → D ≤ n + 6 → SolverAt P fd D (n * D * (n * D)) S)
    (hn : 0 < n) (X Y : SimpleGraph (Fin n)) (hdX : ∀ u, degL X u ≤ d) (hdY : ∀ u, degL Y u ≤ d) :
    FunAll P f (inVal X Y) fun w cost => AnswerOK X Y w ∧ cost ≤ bodyC h S n := by
  classical
  have h0 := WB_ge n
  have hlk := le_kB n
  have wI := inVal_wt X Y
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have hAL : 4 * WB n + 6 ≤ AL n := by
    have := Nat.mul_le_mul_right (2 * WB n + 1) (show 2 ≤ n ^ 2 * (n ^ 2 + 2) + 2 by omega)
    simp only [AL]
    omega
  set I := inVal X Y with hI
  set T := bodyT h S n with hT
  have hTI : 2 * I.wt + 100 ≤ T := by simp only [hT, bodyT]; omega
  have hTW : 1000 * WB n + 1000 * AL n + 1000 * OW n ≤ T := by simp only [hT, bodyT]; omega
  have ga : ∀ rest {k : ℕ} {x : Val}, [Val.nat n, adjVal X, adjVal Y][k]? = some x → k ≤ 2 →
      Lv P (I :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * I.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  set R' : Val → Prop := fun w => AnswerOK X Y w ∧ w.wt ≤ T with hR'
  -- the range
  have hRC : rngC n ≤ T := by simp only [hT, bodyT]; omega
  have cR := Lv.call (ga [] (k := 0) rfl (by omega)) (rng_spec hB.rng (n := n) (m := n) (by omega))
    hRC
  have wR := cR.wt_lt
  refine FunAll.intro hM ((giLet_lv (R := R') (K := 1000000000 * T) cR ?_).mono
    fun w c hw => ⟨hw.1.1, by simp only [bodyC]; exact hw.2⟩)
  -- the largest degree
  have cD := Lv.mk3 (Lv.mk3 (ga [ids n] (k := 1) rfl (by omega)) (ga [ids n] (k := 2) rfl (by omega))
    (Lv.var (P := P) (T := T) (env := [I, ids n]) (i := 1) (v := ids n) rfl (by omega)) (by omega))
    (ga [ids n] (k := 0) rfl (by omega)) (n9 [I, ids n] 0 (by omega)) (by omega)
  have wD := cD.wt_lt
  refine (giLetCall (R := R') (K := 999000000 * T) cD (deg_spec hB.deg X Y) fun w c hw => ?_).mono
    fun w c hw => ⟨hw.1, by have := hw.1.2; have := hw.2; omega⟩
  obtain ⟨⟨m, rfl, hmn, hall, hmin⟩, hc1⟩ := hw
  have hc1' : degLC n ≤ T := by simp only [hT, bodyT]; omega
  have wm : (Val.nat m).wt ≤ WB n := nat_wt (by omega)
  set D := m + 6 with hD
  have hmd : m ≤ d := hmin d fun u => ⟨hdX u, hdY u⟩
  have hS : Sz n D := ⟨hn, by omega, by omega⟩
  have hSol' := hSol D (by omega) (by omega) (by omega)
  have dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D := fun ℓ u =>
    (fwd_le_degL ℓ X u).trans (by have := (hall u).1; omega)
  have dXX : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U X) u).length ≤ D :=
    fun ℓ U u => (fwd_le_degL ℓ _ u).trans (by rw [degL_pull]; have := (hall (U u)).1; omega)
  have dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D :=
    fun ℓ U u => (fwd_le_degL ℓ _ u).trans (by rw [degL_pull]; have := (hall (U u)).2; omega)
  -- the contexts
  have hcT : 1000000000 * ctxT n ≤ T := by simp only [hT, bodyT]; omega
  have cC := Lv.call (Lv.mk3 (Lv.var (P := P) (T := T) (env := [I, ids n, .nat m]) (i := 0) (v := I)
    rfl (by omega)) (Lv.var (P := P) (T := T) (env := [I, ids n, .nat m]) (i := 1) (v := ids n) rfl
    (by omega)) (Lv.var (P := P) (T := T) (env := [I, ids n, .nat m]) (i := 2) (v := .nat m) rfl
    (by omega)) (by omega)) (ctx_spec hB.ctx hB.rng X Y hmn) hcT
  have wC := cC.wt_lt
  refine (giLet_lv (R := R') (K := 998000000 * T) cC ?_).mono
    fun w c hw => ⟨hw.1, by have := hw.1.2; omega⟩
  set C2 := Val.list [riCtx D X X, riCtx D X Y] with hC2
  have wcx := riCtx_wt hS X X
  have wcy := riCtx_wt hS X Y
  have wC2 : C2.wt ≤ 2 * (2 * (9 * (2 * WB n + 1) + 4) + 1) + 4 := wt_lit _ (by
    simp only [hC2, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)
  -- the generators
  have hAu : autLC h S n ≤ T := by simp only [hT, bodyT]; omega
  set E3 := [I, ids n, .nat m, C2] with hE3
  have v3 : Lv P E3 T (.var 3) C2 1 := Lv.var rfl (by omega)
  have gx := Lv.get (vs := [riCtx D X X, riCtx D X Y]) v3 (n9 E3 0 (by omega)) rfl
  have wnn : (Val.nat (n * n)).wt ≤ WB n := nat_wt (by have := sq_le_kB n; omega)
  have cA := Lv.mk3 gx (Lv.arith (op := .mul) (z := n * n) (ga [ids n, .nat m, C2] (k := 0) rfl
    (by omega)) (ga [ids n, .nat m, C2] (k := 0) rfl (by omega)) rfl (by
      have := sq_le_kB n; omega)) (Lv.nil (by omega)) (by omega)
  have wA := cA.wt_lt
  refine (giLetCall (R := R') (K := 997000000 * T) cA (aut_spec h hB.aut hj hSol' hS X dX dXX)
    fun w c hw => ?_).mono fun w c hw => ⟨hw.1, by have := hw.1.2; omega⟩
  obtain ⟨⟨L, rfl, hlen, hgen⟩, hc2⟩ := hw
  have wL : (Val.list (L.map encPerm)).wt ≤ AL n := permList_AL (by omega)
  -- the isomorphism
  have hIs : isoLC h S n ≤ T := by simp only [hT, bodyT]; omega
  have hTb : tbC n ≤ T := by simp only [hT, bodyT]; omega
  set E4 := [I, ids n, .nat m, C2, .list (L.map encPerm)] with hE4
  have v3' : Lv P E4 T (.var 3) C2 1 := Lv.var rfl (by omega)
  have gy := Lv.get (vs := [riCtx D X X, riCtx D X Y]) v3' (n9 E4 1 (by omega)) rfl
  have g0 := ga [ids n, .nat m, C2, .list (L.map encPerm)] (k := 0) rfl (by omega)
  have cT := Lv.call (Lv.mk2 g0 (Lv.var (P := P) (T := T) (env := E4) (i := 1) (v := ids n) rfl
    (by omega)) (by omega)) (tb_spec hB.tab) hTb
  have cI := Lv.mk3 gy g0 (Lv.mk2 cT (n9 E4 1 (by omega)) (by omega)) (by omega)
  have wIv := cI.wt_lt
  refine (giLetCall (R := R') (K := 996000000 * T) cI
    (iso_spec h hB.iso hj hSol' hS X Y dX dY) fun w c hw => ?_).mono
    fun w c hw => ⟨hw.1, by have := hw.1.2; omega⟩
  obtain ⟨hinv, hc3⟩ := hw
  have wo := isoInv_wt hinv
  set E5 := [I, ids n, .nat m, C2, .list (L.map encPerm), w] with hE5
  have v5 : Lv P E5 T (.var 5) w 1 := Lv.var rfl (by omega)
  have v4 : Lv P E5 T (.var 4) (.list (L.map encPerm)) 1 := Lv.var rfl (by omega)
  rcases isoInv_final hinv with ⟨σ, rfl⟩ | ⟨⟨t, rfl⟩, hE⟩
  · have c0 := Lv.get (vs := [encPerm σ.toEquiv, .nat 1]) v5 (n9 E5 1 (by omega)) rfl
    have gs := Lv.get (vs := [encPerm σ.toEquiv, .nat 1]) v5 (n9 E5 0 (by omega)) rfl
    have hO : 1000 * outT n ≤ T := by simp only [hT, bodyT]; omega
    have cO := Lv.call (Lv.mk2 gs v4 (by omega)) (out_spec hB.out σ.toEquiv L
      (by simp only [GLn]; omega)) hO
    have l := Lv.mono (Lv.ite_pos (e := mk1 (.nat 0)) c0 one_ne_zero cO)
      (show _ ≤ 1000 by norm_num)
    have wY := yesCells_wt σ.toEquiv L (by simp only [GLn]; omega)
    refine Det.post l fun c' hc' => ⟨⟨answerOK_yes σ L hgen, by omega⟩, ?_⟩
    have := hc2.trans hAu
    have := hc3.trans hIs
    omega
  · have c0 := Lv.get (vs := [t, .nat 0]) v5 (n9 E5 1 (by omega)) rfl
    have l := Lv.mono (Lv.ite_zero (t := .call out (mk2 (.get (.var 5) (.nat 0)) (.var 4))) c0
      (Lv.mk1 (n9 E5 0 (by omega)) (by omega))) (show _ ≤ 1000 by norm_num)
    have w0 : (Val.list [.nat 0]).wt ≤ 3 * WB n := by
      have h1 : (Val.nat 0).wt ≤ WB n := nat_wt (by omega)
      have := wt_lit (c := WB n) [Val.nat 0] (by simp; exact h1)
      simp only [List.length_singleton] at this
      omega
    refine Det.post l fun c' hc' => ⟨⟨answerOK_no hE, by omega⟩, ?_⟩
    have := hc2.trans hAu
    have := hc3.trans hIs
    omega

end GI.Degree
