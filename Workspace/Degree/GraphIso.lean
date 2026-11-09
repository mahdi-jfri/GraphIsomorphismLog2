module

public import Workspace.Degree.GraphAut

/-!
# An isomorphism, one component at a time

Lemma 9.6 of the paper. The loop runs over the points `v` of `X`. If `v` is not
yet mapped, it looks for the first free `w` with a rooted isomorphism from `v` to `w`, and maps the
component of `v` by it. The invariant (`IsoInv`) is that some isomorphism agrees with the partial
map, whenever there is an isomorphism at all.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- A partial map as a table: `n` for no value. -/
def optN (n : ℕ) (a : Option (Fin n)) : ℕ := a.elim n fun x => x

theorem optN_le (a : Option (Fin n)) : optN n a ≤ n := by
  cases a with
  | none => exact le_rfl
  | some x => exact x.isLt.le

theorem optN_eq_n {a : Option (Fin n)} : optN n a = n ↔ a = none := by
  cases a with
  | none => simp [optN]
  | some x => simp [optN, x.isLt.ne]

theorem optN_eq_val {a : Option (Fin n)} {w : Fin n} : optN n a = w ↔ a = some w := by
  cases a with
  | none => simp [optN, w.isLt.ne']
  | some x => simp [optN, Fin.ext_iff]

theorem eqTest_lv {P : Program} {f : Fin n → ℕ} (hf : ∀ u, f u ≤ n) {t : ℕ} (ht : t ≤ n)
    (u : Fin n) :
    Lv P [.list [.list [encFun f, .nat t], .nat u]] (rkT n) chkTestE
      (boolVal (@decide (f u = t) (Classical.propDecidable _))) 100 := by
  have h0 := levB_pos n
  have h1 := le_levB n
  have wf : (encFun f).wt ≤ levB n := wt_table_le hf
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have wn : (Val.nat t).wt ≤ levB n := wt_nat_levB (by omega)
  have w2 : (Val.list [encFun f, .nat t]).wt ≤ 2 * (2 * levB n + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w3 : (Val.list [.list [encFun f, .nat t], .nat u]).wt ≤
      2 * (2 * ((Val.list [encFun f, .nat t]).wt + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : rkT n = 1000 * levB n := rfl
  set E := [Val.list [.list [encFun f, .nat t], .nat u]] with hE
  have a0 : Lv P E (rkT n) (arg 0) (.list [encFun f, .nat t]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (rkT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have gf := Lv.get (vs := [encFun f, .nat t]) a0 (Lv.nat 0 (by omega)) rfl
  have gn := Lv.get (vs := [encFun f, .nat t]) a0 (Lv.nat 1 (by omega)) rfl
  have hfu := hf u
  have e1 := Lv.arith (op := .eq) (z := if f u = t then 1 else 0) (Lv.tget gf a1) gn rfl
    (by split <;> omega)
  classical
  rw [boolVal_ite]
  exact Lv.mono (e := chkTestE) e1 (by norm_num)

/-- The entry of the update, on `[[τ, lv, p, n], u]`. -/
def updE : Expr :=
  let c := arg 0
  .ite (.arith .lt (.get (.get c (.nat 1)) (arg 1)) (.get c (.nat 3))) (.get (.get c (.nat 0)) (arg 1))
    (.get (.get c (.nat 2)) (arg 1))

/-- The context of the update. -/
noncomputable def updCtx (X : SimpleGraph (Fin n)) (v : Fin n) (τ : Perm (Fin n))
    (p : Fin n → Option (Fin n)) : Val :=
  .list [encPerm τ, encFun (lev X v), encFun fun u => optN n (p u), .nat n]

set_option maxHeartbeats 1000000 in
theorem updE_lv {P : Program} (X : SimpleGraph (Fin n)) (v : Fin n) (τ : Perm (Fin n))
    (p : Fin n → Option (Fin n)) (u : Fin n) :
    Lv P [.list [updCtx X v τ p, .nat u]] (swT n) updE
      (.nat (optN n (addComp X p v τ u))) 1000 := by
  classical
  have h0 := levB_pos n
  have hl := le_levB n
  have w1 : (encPerm τ).wt ≤ levB n := by
    rw [encPerm_eq_encFun]; exact wt_table_le fun i => (τ i).isLt.le
  have w2 : (encFun (lev X v)).wt ≤ levB n := wt_table_le (lev_le X v)
  have w3 : (encFun fun u => optN n (p u)).wt ≤ levB n := wt_table_le fun u => optN_le _
  have w4 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have wc : (updCtx X v τ p).wt ≤ 4 * (2 * levB n + 1) + 4 := wt_lit _ (by
    simp only [updCtx, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have w5 : (Val.list [updCtx X v τ p, .nat u]).wt ≤
      2 * (2 * (4 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : swT n = 1000 * levB n := rfl
  set E := [Val.list [updCtx X v τ p, .nat u]] with hE
  have a0 : Lv P E (swT n) (arg 0) (.list [encFun fun i => (τ i : ℕ), encFun (lev X v),
      encFun fun u => optN n (p u), .nat n]) 1 := by
    have := Lv.arg (P := P) (rest := []) (vs := [updCtx X v τ p, .nat u]) (j := 0) (T := swT n) rfl
      (by omega)
    rwa [updCtx, encPerm_eq_encFun] at this
  have a1 : Lv P E (swT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 3 → Lv P E (swT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have g := fun k (hk : k ≤ 3) {x : Val} (hx : [encFun fun i => (τ i : ℕ), encFun (lev X v),
      encFun fun u => optN n (p u), Val.nat n][k]? = some x) => Lv.get a0 (n0 k hk) hx
  have gt := Lv.tget (g 0 (by omega) rfl) a1
  have gv := Lv.tget (g 1 (by omega) rfl) a1
  have gp := Lv.tget (g 2 (by omega) rfl) a1
  have gn := g 3 (by omega) rfl
  have hv := lev_le X v u
  have c1 := Lv.arith (op := .lt) (z := if lev X v u < n then 1 else 0) gv gn rfl (by split <;> omega)
  by_cases h1 : X.Reachable v u
  · rw [if_pos (lev_lt_iff.2 h1)] at c1
    rw [addComp_new h1]
    exact Lv.mono (e := updE) (Lv.ite_pos (e := .get _ _) c1 (by omega) gt) (by norm_num)
  · rw [if_neg (fun h => h1 (lev_lt_iff.1 h))] at c1
    rw [addComp_old h1]
    exact Lv.mono (e := updE) (Lv.ite_zero (t := _) c1 gp) (by norm_num)

theorem upd_spec {P : Program} {a : ℕ} (h : P.HasAt a (tabFuns a updE)) (X : SimpleGraph (Fin n))
    (v : Fin n) (τ : Perm (Fin n)) (p : Fin n → Option (Fin n)) :
    FunDet P a (.list [updCtx X v τ p, ids n]) (encFun fun u => optN n (addComp X p v τ u))
      (swC n) := by
  have h0 := levB_pos n
  have hl := le_levB n
  have w1 : (encPerm τ).wt ≤ levB n := by
    rw [encPerm_eq_encFun]; exact wt_table_le fun i => (τ i).isLt.le
  have w2 : (encFun (lev X v)).wt ≤ levB n := wt_table_le (lev_le X v)
  have w3 : (encFun fun u => optN n (p u)).wt ≤ levB n := wt_table_le fun u => optN_le _
  have w4 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  have wc : (updCtx X v τ p).wt ≤ 4 * (2 * levB n + 1) + 4 := wt_lit _ (by
    simp only [updCtx, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have w6 : (encFun fun u => optN n (addComp X p v τ u)).wt ≤ levB n :=
    wt_table_le fun u => optN_le _
  have w5 : (Val.list [updCtx X v τ p, ids n]).wt ≤
      2 * (2 * (4 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : swT n = 1000 * levB n := rfl
  exact tabN_spec (T := swT n) (K := 1000) (W := swT n) h (fun u => updE_lv X v τ p u) (by omega)

/-- The test of the search, on `[[riCtx D X Y, p, v], w]`: `w` is free and there is a rooted
isomorphism from `v` to `w`. -/
def isoTestE (anyB ri : ℕ) : Expr :=
  .letE (.call anyB (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1)) (.get (.get (arg 0) (.nat 0)) (.nat 3))))
    (.ite (.var 1) (.nat 0)
      (.ite (.length (.call ri (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2)) (arg 1))))
        (.nat 1) (.nat 0)))

/-- A bound on small weights. -/
def tW (n : ℕ) : ℕ := 1000 * WB n

/-- The cost of the test for a free point. -/
def anyC' (n : ℕ) : ℕ := n * (100 * rkT n) + loopModK * (n + 1) * tW n

/-- The budget of the test. -/
noncomputable def testT (h : Membership) (S n : ℕ) : ℕ := riC h S n + anyC' n + tW n

/-- The bound of the test. -/
noncomputable def testC (h : Membership) (S n : ℕ) : ℕ := 10000000 * testT h S n

/-- The test. -/
def IsoQ (X Y : SimpleGraph (Fin n)) (pn : Fin n → ℕ) (v w : Fin n) : Prop :=
  (¬∃ u, pn u = w) ∧ ∃ g, IsRooted X v Y w g

set_option maxHeartbeats 4000000 in
theorem isoTest_spec {P : Program} {f anyB ri fd j S : ℕ} (h : Membership)
    (hf : P.funs[f]? = some (isoTestE anyB ri)) (hAny : P.HasAt anyB (anyFuns anyB (anyB + 3)))
    (hEq : P.funs[anyB + 3]? = some chkTestE) (hRi : P.HasAt ri (riFuns ri fd j))
    (hj : P.prims[j]? = some (membershipPrim h)) (hSol : SolverAt P fd D (n * D * (n * D)) S)
    (hS : Sz n D) (X Y : SimpleGraph (Fin n)) (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D)
    {pn : Fin n → ℕ} (hpn : ∀ u, pn u ≤ n) (v w : Fin n) :
    FunDet P f (.list [.list [riCtx D X Y, encFun pn, .nat v], .nat w])
      (boolVal (@decide (IsoQ X Y pn v w) (Classical.propDecidable _))) (testC h S n) := by
  classical
  have h0 := WB_ge n
  have hlk := le_kB n
  have hlB := levB_le_WB n
  have hlp := levB_pos n
  have wc := riCtx_wt hS X Y
  have wp : (encFun pn).wt ≤ WB n := table_wt (by omega) hpn
  have wv : (Val.nat v).wt ≤ WB n := fin_wt (by omega) v
  have ww : (Val.nat w).wt ≤ WB n := fin_wt (by omega) w
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  set c := Val.list [riCtx D X Y, encFun pn, .nat v] with hc
  have w1 : c.wt ≤ 3 * (2 * (9 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [hc, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  set A := Val.list [c, .nat w] with hA
  have w2 : A.wt ≤ 2 * (2 * (c.wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w3 : (Val.list [encFun pn, .nat w]).wt ≤ 2 * (2 * WB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w4 : (Val.list [.list [encFun pn, .nat w], ids n]).wt ≤
      2 * (2 * (2 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : tW n = 1000 * WB n := rfl
  have hrk : rkT n = 1000 * levB n := rfl
  set T := testT h S n with hT
  have hTr : riC h S n + anyC' n + tW n ≤ T := le_rfl
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, testT, tW] at *; omega
  have a0 : ∀ rest, Lv P (A :: rest) T (arg 0) c 1 := fun rest =>
    Lv.arg (vs := [c, .nat w]) rfl (by change 2 * A.wt + 0 + 5 ≤ T; omega)
  have a1 : ∀ rest, Lv P (A :: rest) T (arg 1) (.nat w) 1 := fun rest =>
    Lv.arg (vs := [c, .nat w]) rfl (by change 2 * A.wt + 1 + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 3 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gc := fun rest (k : ℕ) (hk : k ≤ 3) {x : Val}
      (hx : [riCtx D X Y, encFun pn, Val.nat v][k]? = some x) =>
    Lv.get (vs := [riCtx D X Y, encFun pn, .nat v]) (a0 rest) (n9 _ k hk) hx
  have gi := fun rest => Lv.get (vs := [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (gc rest 0 (by omega) rfl)
      (n9 _ 3 le_rfl) rfl
  have hany := anyFin_spec (c := .list [encFun pn, .nat w]) hAny (fun u => pn u = w)
    (B := 100 * rkT n) (fun u => funDet_of_lv hEq (eqTest_lv hpn w.isLt.le u))
  have e2 : loopModK * (n + 1) * ((Val.list [.list [encFun pn, .nat w], ids n]).wt + n + 4) ≤
      loopModK * (n + 1) * tW n := Nat.mul_le_mul_left _ (by omega)
  have cAny := Lv.mono (Lv.call (Lv.mk2 (Lv.mk2 (gc [] 1 (by omega) rfl) (a1 []) (by omega)) (gi [])
    (by omega)) hany (by simp only [hT, testT, anyC']; omega)) (show _ ≤ 1000 by norm_num)
  refine FunDet.intro hf (EvalAll.letE cAny fun x1 c1 hx1 => ?_)
  have hc1 := hx1.2
  have hTW : WB n ≤ T := by simp only [hT, testT, tW] at *; omega
  have hn : 1 ≤ n := by have := v.isLt; omega
  have hk : ∃ k1 : ℕ, x1 = .nat k1 ∧ (k1 = 0 ↔ ¬∃ z, pn z = w) ∧ k1 ≤ 1 := by
    rw [hx1.1]; split_ifs with hh <;> simp [hh]
  obtain ⟨k1, rfl, hk0, hk1⟩ := hk
  have wk1 : (Val.nat k1).wt ≤ levB n := wt_nat_levB (by omega)
  have v1 : Lv P ([A] ++ [.nat k1]) T (.var 1) (.nat k1) 1 := Lv.var rfl (by omega)
  refine EvalAll.ite (Lv.mono v1 (le_refl 1)) (fun vc cc hc => ⟨k1, hc.1⟩) fun x cx hx => ?_
  obtain ⟨hx, hcx⟩ := hx
  obtain rfl : k1 = x := by injection hx.symm
  by_cases hex : ∃ z, pn z = w
  · have e1 : k1 = 1 := by
      have : k1 ≠ 0 := fun h0 => hk0.1 h0 hex
      omega
    rw [if_neg (show k1 ≠ 0 by omega)]
    have hq : ¬IsoQ X Y pn v w := fun hq => hq.1 hex
    rw [show boolVal (@decide (IsoQ X Y pn v w) (Classical.propDecidable _)) = .nat 0 by
      simp [hq, boolVal]]
    refine Det.post (Lv.mono (n9 [A, .nat k1] 0 (by omega)) (le_refl 1)) fun c' hc' => ⟨rfl, ?_⟩
    have := wt_nat_levB (n := n) (k := 0) (by omega)
    show _ ≤ 10000000 * T
    omega
  · have e1 : k1 = 0 := hk0.2 hex
    rw [if_pos e1]
    have hri := ri_spec h hRi hj hSol hS X Y dX dY v w
    have cA := Lv.mono (Lv.mk3 (gc [.nat k1] 0 (by omega) rfl) (gc [.nat k1] 2 (by omega) rfl)
      (a1 [.nat k1]) (by omega)) (show _ ≤ 1000 by norm_num)
    have hR : ∀ (x : ℕ), x = (if ∃ g, IsRooted X v Y w g then 2 else 0) → x = 0 ∨ x = 2 := by
      intro x hx
      split_ifs at hx <;> omega
    refine EvalAll.ite (Rc := fun vc cc => vc = .nat (if ∃ g, IsRooted X v Y w g then 2 else 0) ∧
        cc ≤ 1000 * T + riC h S n + riC h S n + 2 * T + 10)
      (EvalAll.length (Ra := fun out c => RIOut X v Y w out ∧ c ≤ 1000 * T + riC h S n +
          riC h S n + 1 ∧ out.wt < riC h S n)
        (EvalAll.call_funAll cA fun va ca hva => ?_) fun out cout hout => ?_)
      (fun vc cc hc => ⟨_, hc.1⟩) fun x cx' hx' => ?_
    · obtain ⟨rfl, hca⟩ := hva
      refine FunAll.mono hri.wt_lt fun y cy hy => ⟨hy.1.1, ?_, ?_⟩
      · have := hy.1.2
        have := hy.2
        omega
      · have := hy.1.2
        have := hy.2
        omega
    · obtain ⟨hRO, hco, hwo⟩ := hout
      rcases hRO with ⟨rfl, hno⟩ | ⟨τ, gs, rfl, hτ, -, -⟩
      · refine ⟨[], rfl, ?_, ?_⟩
        · rw [if_neg (fun ⟨g, hg⟩ => hno g hg)]
          rfl
        · have := wt_nat_levB (n := n) (k := 0) (by omega)
          simp only [List.length_nil]
          omega
      · refine ⟨_, rfl, ?_, ?_⟩
        · rw [if_pos ⟨τ, hτ⟩]
          rfl
        · have := wt_nat_levB (n := n) (k := 2) (by omega)
          simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
          omega
    · obtain ⟨hx2, hcx2⟩ := hx'
      have hxv : x = if ∃ g, IsRooted X v Y w g then 2 else 0 := by injection hx2
      by_cases hg : ∃ g, IsRooted X v Y w g
      · rw [if_pos hg] at hxv
        subst hxv
        rw [if_neg (by norm_num)]
        have hq : IsoQ X Y pn v w := ⟨hex, hg⟩
        rw [show boolVal (@decide (IsoQ X Y pn v w) (Classical.propDecidable _)) = .nat 1 by
          simp [hq, boolVal]]
        refine Det.post (Lv.mono (n9 [A, .nat k1] 1 (by omega)) (le_refl 1)) fun c' hc' => ⟨rfl, ?_⟩
        have := wt_nat_levB (n := n) (k := 1) (by omega)
        show _ ≤ 10000000 * T
        omega
      · rw [if_neg hg] at hxv
        subst hxv
        rw [if_pos rfl]
        have hq : ¬IsoQ X Y pn v w := fun hq => hg hq.2
        rw [show boolVal (@decide (IsoQ X Y pn v w) (Classical.propDecidable _)) = .nat 0 by
          simp [hq, boolVal]]
        refine Det.post (Lv.mono (n9 [A, .nat k1] 0 (by omega)) (le_refl 1)) fun c' hc' => ⟨rfl, ?_⟩
        have := wt_nat_levB (n := n) (k := 0) (by omega)
        show _ ≤ 10000000 * T
        omega

/-- An `if` whose test has a known value. -/
theorem giIte_lv {P : Program} {env : List Val} {T : ℕ} {c t e : Expr} {x m K : ℕ}
    {R : Val → Prop} (hc : Lv P env T c (.nat x) m)
    (ht : x ≠ 0 → EvalAll P env t fun w cb => R w ∧ m * T + cb + w.wt + 1 ≤ K)
    (he : x = 0 → EvalAll P env e fun w cb => R w ∧ m * T + cb + w.wt + 1 ≤ K) :
    EvalAll P env (.ite c t e) fun w cost => R w ∧ cost ≤ K := by
  refine .ite hc (fun vc cc h => ⟨x, h.1⟩) fun y cy hy => ?_
  obtain ⟨hy1, hy2⟩ := hy
  have hyx : y = x := by injection hy1
  subst hyx
  by_cases h0 : y = 0
  · rw [if_pos h0]
    exact (he h0).mono fun w cb hw => ⟨hw.1, by omega⟩
  · rw [if_neg h0]
    exact (ht h0).mono fun w cb hw => ⟨hw.1, by omega⟩

/-- A `let` whose bound value is known. -/
theorem giLet_lv {P : Program} {env : List Val} {T : ℕ} {e body : Expr} {v : Val} {m K : ℕ}
    {R : Val → Prop} (ha : Lv P env T e v m)
    (hb : EvalAll P (env ++ [v]) body fun w cb => R w ∧ m * T + cb + w.wt + 1 ≤ K) :
    EvalAll P env (.letE e body) fun w cost => R w ∧ cost ≤ K :=
  .letE ha fun v' ca h => by
    obtain ⟨rfl, hca⟩ := h
    exact hb.mono fun w cb hw => ⟨hw.1, by omega⟩

/-- A call on a known argument. -/
theorem giCall_lv {P : Program} {env : List Val} {T : ℕ} {f : ℕ} {a : Expr} {x : Val} {m K : ℕ}
    {R : Val → Prop} (ha : Lv P env T a x m)
    (hf : FunAll P f x fun w cb => R w ∧ m * T + cb + w.wt + 1 ≤ K) :
    EvalAll P env (.call f a) fun w cost => R w ∧ cost ≤ K :=
  EvalAll.call_funAll ha fun v ca h => by
    obtain ⟨rfl, hca⟩ := h
    exact hf.mono fun w cb hw => ⟨hw.1, by omega⟩

/-- Extend the partial map by a rooted isomorphism from `v` to `w`, on `[c, v, w, p]`. -/
def extE (ri lv upd : ℕ) : Expr :=
  let c := arg 0
  let nn := Expr.get c (.nat 2)
  .letE (.call ri (mk3 c (arg 1) (arg 2)))
    (.letE (.call lv (mk4 (.get c (.nat 0)) nn (.get c (.nat 3)) (arg 1)))
      (mk2 (.call upd (mk2 (mk4 (.get (.var 1) (.nat 0)) (.var 2) (arg 3) nn) (.get c (.nat 3))))
        (.nat 1)))

/-- The budget of the extension. -/
noncomputable def extT (h : Membership) (S n : ℕ) : ℕ := riC h S n + levC n + swC n + 1000 * WB n

/-- The bound of the extension. -/
noncomputable def extC (h : Membership) (S n : ℕ) : ℕ := 10000000 * extT h S n

set_option maxHeartbeats 4000000 in
theorem ext_spec {P : Program} {a ri lv upd fd j S : ℕ} (h : Membership)
    (hf : P.funs[a]? = some (extE ri lv upd)) (hRi : P.HasAt ri (riFuns ri fd j))
    (hLv : P.HasAt lv (levFuns lv)) (hU : P.HasAt upd (tabFuns upd updE))
    (hj : P.prims[j]? = some (membershipPrim h)) (hSol : SolverAt P fd D (n * D * (n * D)) S)
    (hS : Sz n D) (X Y : SimpleGraph (Fin n)) (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D)
    (p : Fin n → Option (Fin n)) (v w : Fin n) (hq : ∃ g, IsRooted X v Y w g) :
    FunAll P a (.list [riCtx D X Y, .nat v, .nat w, encFun fun u => optN n (p u)])
      fun out cost => (∃ τ, IsRooted X v Y w τ ∧
        out = .list [encFun fun u => optN n (addComp X p v τ u), .nat 1]) ∧ cost ≤ extC h S n := by
  classical
  have hn : 0 < n := hS.pos
  have h0 := WB_ge n
  have hk := hS.k_le
  have hlk := le_kB n
  have hlB := levB_le_WB n
  have wc := riCtx_wt hS X Y
  have wp : (encFun fun u => optN n (p u)).wt ≤ WB n := table_wt (by omega) fun u => optN_le _
  have wv : (Val.nat v).wt ≤ WB n := fin_wt (by omega) v
  have ww : (Val.nat w).wt ≤ WB n := fin_wt (by omega) w
  have wlv : (encFun (lev X v)).wt ≤ WB n := table_wt (by omega) (lev_le X v)
  have w1 : (Val.nat 1).wt ≤ WB n := nat_wt (by omega)
  set A := Val.list [riCtx D X Y, .nat v, .nat w, encFun fun u => optN n (p u)] with hA
  have wA : A.wt ≤ 4 * (2 * (9 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [hA, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl) <;> omega)
  set T := extT h S n with hT
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, extT]; omega
  have hTr : riC h S n + levC n + swC n + 1000 * WB n ≤ T := le_rfl
  have ga : ∀ rest {k : ℕ} {x : Val},
      [riCtx D X Y, .nat v, .nat w, encFun fun u => optN n (p u)][k]? = some x →
      k ≤ 3 → Lv P (A :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gc : ∀ rest (k : ℕ) {x : Val}, [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))][k]? = some x → k ≤ 8 →
      Lv P (A :: rest) T (.get (arg 0) (.nat k)) x _ := fun rest k x hx hk =>
    Lv.get (vs := [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (ga rest (k := 0) rfl (by omega))
      (n9 _ k hk) hx
  have cA := Lv.mono (Lv.mk3 (ga [] (k := 0) rfl (by omega)) (ga [] (k := 1) rfl (by omega))
    (ga [] (k := 2) rfl (by omega)) (by omega)) (show _ ≤ 1000 by norm_num)
  have hri := ri_spec h hRi hj hSol hS X Y dX dY v w
  refine FunAll.intro hf (EvalAll.letE (Ra := fun out c => RIOut X v Y w out ∧
      c ≤ 1000 * T + riC h S n + riC h S n + 1 ∧ out.wt < riC h S n)
    (EvalAll.call_funAll cA fun va ca hva => ?_) fun out cout hout => ?_)
  · obtain ⟨rfl, hca⟩ := hva
    refine FunAll.mono hri.wt_lt fun x c hx => ⟨hx.1.1, ?_, ?_⟩
    · have := hx.1.2
      have := hx.2
      omega
    · have := hx.1.2
      have := hx.2
      omega
  obtain ⟨hRO, hcout, hwout⟩ := hout
  rcases hRO with ⟨rfl, hno⟩ | ⟨τ, gs, rfl, hτ, -, -⟩
  · obtain ⟨g, hg⟩ := hq
    exact (hno g hg).elim
  set O := Val.list [encPerm τ, encGroup gs] with hO
  have hlv := lev_spec hLv X v
  have cLv := Lv.call (Lv.mk4 (gc [O] 0 rfl (by omega)) (gc [O] 2 rfl (by omega))
    (gc [O] 3 rfl (by omega)) (ga [O] (k := 1) rfl (by omega)) (by omega)) hlv (by omega)
  set E2 := [A, O, encFun (lev X v)] with hE2
  have v1 : Lv P E2 T (.var 1) O 1 := Lv.var rfl (by omega)
  have gτ := Lv.get (vs := [encPerm τ, encGroup gs]) v1 (n9 E2 0 (by omega)) rfl
  have vl : Lv P E2 T (.var 2) (encFun (lev X v)) 1 := Lv.var rfl (by omega)
  have cU := Lv.call (Lv.mk2 (Lv.mk4 gτ vl (ga [O, encFun (lev X v)] (k := 3) rfl (by omega))
    (gc [O, encFun (lev X v)] 2 rfl (by omega)) (by omega))
    (gc [O, encFun (lev X v)] 3 rfl (by omega)) (by omega)) (upd_spec hU X v τ p) (by omega)
  have cM := Lv.mk2 cU (n9 E2 1 (by omega)) (by omega)
  have l1 := Lv.mono (Lv.letE cLv cM) (show _ ≤ 100000 by norm_num)
  have wl := l1.wt_lt
  refine Det.post l1 fun c' hc' => ⟨⟨τ, hτ, rfl⟩, ?_⟩
  simp only [extC]
  omega

open Classical in
/-- What the first index found by a search over `Fin n` says. -/
theorem findIdx_fin (q : Fin n → Prop) :
    ((List.finRange n).findIdx fun z => decide (q z)) ≤ n ∧
    (∀ hk : (List.finRange n).findIdx (fun z => decide (q z)) < n,
      q ⟨(List.finRange n).findIdx fun z => decide (q z), hk⟩) ∧
    ((List.finRange n).findIdx (fun z => decide (q z)) = n → ∀ z, ¬q z) := by
  refine ⟨by simpa using List.findIdx_le_length (p := fun z => decide (q z)) (xs := List.finRange n),
    fun hk => ?_, fun hk z hz => ?_⟩
  · have hk' : (List.finRange n).findIdx (fun z => decide (q z)) < (List.finRange n).length := by
      simpa using hk
    have := List.findIdx_getElem (w := hk')
    rw [List.getElem_finRange] at this
    simpa using this
  · have h1 := (List.findIdx_eq_length (p := fun z => decide (q z)) (xs := List.finRange n)).1
      (by simpa using hk) z (List.mem_finRange z)
    simp [hz] at h1

/-- The search for an image of `v`, on `[c, p, v]`. -/
def searchE (fnd ext : ℕ) : Expr :=
  let nn := Expr.get (arg 0) (.nat 2)
  .letE (.call fnd (mk2 (.var 0) (.get (arg 0) (.nat 3))))
    (.ite (.arith .lt (.var 1) nn) (.call ext (mk4 (arg 0) (arg 2) (.var 1) (arg 1)))
      (mk2 (arg 1) (.nat 0)))

/-- The output of the search. -/
def SearchOut (X Y : SimpleGraph (Fin n)) (p : Fin n → Option (Fin n)) (v : Fin n) (out : Val) :
    Prop :=
  (∃ w τ, IsoQ X Y (fun u => optN n (p u)) v w ∧ IsRooted X v Y w τ ∧
    out = .list [encFun fun u => optN n (addComp X p v τ u), .nat 1]) ∨
  ((∀ w, ¬IsoQ X Y (fun u => optN n (p u)) v w) ∧
    out = .list [encFun fun u => optN n (p u), .nat 0])

/-- The cost of the find. -/
noncomputable def findC' (h : Membership) (S n : ℕ) : ℕ :=
  n * testC h S n + loopModK * (n + 1) * (1000 * WB n + 2 * n + 3)

/-- The budget of the search. -/
noncomputable def isoSrchT (h : Membership) (S n : ℕ) : ℕ := findC' h S n + extC h S n + 1000 * WB n

/-- The bound of the search. -/
noncomputable def isoSrchC (h : Membership) (S n : ℕ) : ℕ := 10000000 * isoSrchT h S n

set_option maxHeartbeats 4000000 in
theorem search_spec {P : Program} {a fnd ext tst anyB ri lv upd fd j S : ℕ} (h : Membership)
    (hf : P.funs[a]? = some (searchE fnd ext)) (hF : P.HasAt fnd (findFuns fnd tst))
    (hE : P.funs[ext]? = some (extE ri lv upd))
    (hT : P.funs[tst]? = some (isoTestE anyB ri)) (hAny : P.HasAt anyB (anyFuns anyB (anyB + 3)))
    (hEq : P.funs[anyB + 3]? = some chkTestE) (hRi : P.HasAt ri (riFuns ri fd j))
    (hLv : P.HasAt lv (levFuns lv)) (hU : P.HasAt upd (tabFuns upd updE))
    (hj : P.prims[j]? = some (membershipPrim h)) (hSol : SolverAt P fd D (n * D * (n * D)) S)
    (hS : Sz n D) (X Y : SimpleGraph (Fin n)) (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D)
    (p : Fin n → Option (Fin n)) (v : Fin n) :
    FunAll P a (.list [riCtx D X Y, encFun fun u => optN n (p u), .nat v])
      fun out cost => SearchOut X Y p v out ∧ cost ≤ isoSrchC h S n := by
  classical
  have hn : 0 < n := hS.pos
  have h0 := WB_ge n
  have hk := hS.k_le
  have hlk := le_kB n
  have hlB := levB_le_WB n
  have wc := riCtx_wt hS X Y
  have wp : (encFun fun u => optN n (p u)).wt ≤ WB n := table_wt (by omega) fun u => optN_le _
  have wv : (Val.nat v).wt ≤ WB n := fin_wt (by omega) v
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have w0 : (Val.nat 0).wt ≤ WB n := nat_wt (by omega)
  have w1 : (Val.nat 1).wt ≤ WB n := nat_wt (by omega)
  have wn1 : (Val.nat (n + 1)).wt ≤ WB n := nat_wt (by omega)
  set A := Val.list [riCtx D X Y, encFun fun u => optN n (p u), .nat v] with hA
  have wA : A.wt ≤ 3 * (2 * (9 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [hA, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  have wAi : (Val.list [A, ids n]).wt ≤ 2 * (2 * (A.wt + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)
  set T := isoSrchT h S n with hT'
  have hTr : findC' h S n + extC h S n + 1000 * WB n ≤ T := le_rfl
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT', isoSrchT]; omega
  have ga : ∀ rest {k : ℕ} {x : Val},
      [riCtx D X Y, encFun fun u => optN n (p u), .nat v][k]? = some x →
      k ≤ 2 → Lv P (A :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gc : ∀ rest (k : ℕ) {x : Val}, [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))][k]? = some x → k ≤ 8 →
      Lv P (A :: rest) T (.get (arg 0) (.nat k)) x _ := fun rest k x hx hk =>
    Lv.get (vs := [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (ga rest (k := 0) rfl (by omega))
      (n9 _ k hk) hx
  have hfind := findFin_spec (c := A) hF (IsoQ X Y (fun u => optN n (p u)) v) (B := testC h S n)
    fun z => isoTest_spec h hT hAny hEq hRi hj hSol hS X Y dX dY (fun u => optN_le _) v z
  set k := (List.finRange n).findIdx fun z => decide (IsoQ X Y (fun u => optN n (p u)) v z)
    with hkdef
  obtain ⟨hkn, hkq, hkno⟩ := findIdx_fin (IsoQ X Y (fun u => optN n (p u)) v)
  have e2 : loopModK * (n + 1) * ((Val.list [A, ids n]).wt + 2 * n + 3) ≤
      loopModK * (n + 1) * (1000 * WB n + 2 * n + 3) := Nat.mul_le_mul_left _ (by omega)
  have cF := Lv.call (Lv.mk2 (Lv.var (env := [A]) (i := 0) rfl (by omega)) (gc [] 3 rfl (by omega))
    (by omega)) hfind (by simp only [hT', isoSrchT, findC'] at *; omega)
  refine FunAll.intro hf (giLet_lv cF ?_)
  have wk : (Val.nat k).wt ≤ WB n := nat_wt (by omega)
  have vk : Lv P ([A] ++ [.nat k]) T (.var 1) (.nat k) 1 := Lv.var rfl (by omega)
  have cc := Lv.arith (op := .lt) (z := if k < n then 1 else 0) vk (gc [.nat k] 2 rfl (by omega))
    rfl (by split <;> omega)
  have wcF := cF.wt_lt
  refine (giIte_lv (R := fun w => SearchOut X Y p v w ∧ w.wt ≤ T) (K := 9000000 * T) cc
    (fun hx => ?_) fun hx => ?_).mono fun w cb hw => ⟨hw.1.1, ?_⟩
  rotate_left 2
  · have := hw.1.2
    have := hw.2
    simp only [isoSrchC]
    omega
  · have hkl : k < n := by
      by_contra hc
      exact hx (if_neg hc)
    have hq := hkq hkl
    have hext := ext_spec h hE hRi hLv hU hj hSol hS X Y dX dY p v ⟨k, hkl⟩ hq.2
    have cA := Lv.mk4 (ga [.nat k] (k := 0) rfl (by omega)) (ga [.nat k] (k := 2) rfl (by omega))
      vk (ga [.nat k] (k := 1) rfl (by omega)) (by omega)
    have hET : extC h S n ≤ T := by simp only [hT', isoSrchT]; omega
    refine (giCall_lv (R := fun w => SearchOut X Y p v w ∧ w.wt ≤ T) (K := 8000000 * T) cA
      (hext.wt_lt.mono fun out c ho => ⟨⟨Or.inl ?_, ?_⟩, ?_⟩)).mono
      fun w cb hw => ⟨hw.1, by have := hw.2; have := hw.1.2; omega⟩
    · obtain ⟨τ, hτ, rfl⟩ := ho.1.1
      exact ⟨⟨k, hkl⟩, τ, hq, hτ, rfl⟩
    · have := ho.2
      omega
    · have := ho.1.2
      have := ho.2
      have := cc.wt_lt
      omega
  · have hkl : k = n := by
      by_contra hc
      rw [if_pos (show k < n by omega)] at hx
      exact absurd hx (by norm_num)
    have cO := Lv.mono (Lv.mk2 (ga [.nat k] (k := 1) rfl (by omega)) (n9 [A, .nat k] 0 (by omega))
      (by omega)) (show _ ≤ 100 by norm_num)
    have wO : (Val.list [encFun fun u => optN n (p u), .nat 0]).wt ≤ 2 * (2 * WB n + 1) + 4 :=
      wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                   rintro x (rfl | rfl) <;> omega)
    refine Det.post cO fun c' hc' => ⟨⟨Or.inr ⟨hkno hkl, rfl⟩, by omega⟩, ?_⟩
    have := cc.wt_lt
    omega

/-- `g` is an isomorphism from `X` to `Y`. -/
def IsoP (X Y : SimpleGraph (Fin n)) (g : Perm (Fin n)) : Prop := ∀ a b, X.Adj a b ↔ Y.Adj (g a) (g b)

/-- The invariant of the loop over points: the partial map, with `1` while all is well, and `0`
once we know there is no isomorphism. -/
def IsoInv (X Y : SimpleGraph (Fin n)) (i : ℕ) (acc : Val) : Prop :=
  ∃ (p : Fin n → Option (Fin n)) (ok : ℕ), acc = .list [encFun fun u => optN n (p u), .nat ok] ∧
    PartIso X Y p ∧
    ((ok = 1 ∧ (∀ u : Fin n, (u : ℕ) < i → p u ≠ none) ∧
        ((∃ g, IsoP X Y g) → ∃ g, IsoP X Y g ∧ Agree p g)) ∨
      (ok = 0 ∧ ¬∃ g, IsoP X Y g))

theorem isoInv_wt {X Y : SimpleGraph (Fin n)} {i : ℕ} {acc : Val} (h : IsoInv X Y i acc) :
    acc.wt ≤ 2 * (2 * WB n + 1) + 4 := by
  obtain ⟨p, ok, rfl, -, hok⟩ := h
  have h0 := WB_ge n
  have hok1 : ok ≤ 1 := by rcases hok with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have wp : (encFun fun u => optN n (p u)).wt ≤ WB n := table_wt (by omega) fun u => optN_le _
  have wk : (Val.nat ok).wt ≤ WB n := nat_wt (by omega)
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl) <;> omega)

/-- The step at the point `i`, on `[c, i, acc]`. -/
def isoStepE (srch : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 1))
    (.ite (.arith .lt (.get (.get (arg 2) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 2))) (arg 2)
      (.call srch (mk3 (arg 0) (.get (arg 2) (.nat 0)) (arg 1))))
    (arg 2)

/-- The functions of the step. -/
def isoStepFuns (a fd j : ℕ) : List Expr :=
  [isoStepE (a + 1)] ++ [searchE (a + 3) (a + 2)] ++ [extE (a + 15) (a + 16) (a + 11)] ++
    findFuns (a + 3) (a + 6) ++ [isoTestE (a + 7) (a + 15)] ++ anyFuns (a + 7) (a + 10) ++
    [chkTestE] ++ tabFuns (a + 11) updE ++ riFuns (a + 15) fd j

/-- The budget of the step. -/
noncomputable def isoStepT (h : Membership) (S n : ℕ) : ℕ := isoSrchC h S n + 1000 * WB n

/-- The bound of the step. -/
noncomputable def isoStepC (h : Membership) (S n : ℕ) : ℕ := 10000000 * isoStepT h S n

set_option maxHeartbeats 4000000 in
theorem isoStep_spec {P : Program} {a fd j S : ℕ} (h : Membership)
    (hP : P.HasAt a (isoStepFuns a fd j)) (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : SolverAt P fd D (n * D * (n * D)) S) (hS : Sz n D) (X Y : SimpleGraph (Fin n))
    (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D)
    {i : ℕ} (hi : i < n) {acc : Val} (hI : IsoInv X Y i acc) :
    FunAll P a (.list [riCtx D X Y, .nat i, acc]) fun out cost =>
      IsoInv X Y (i + 1) out ∧ cost ≤ isoStepC h S n := by
  classical
  have hM : P.funs[a]? = some (isoStepE (a + 1)) :=
    hP.left.left.left.left.left.left.left.left.single
  have hSr : P.funs[a + 1]? = some (searchE (a + 3) (a + 2)) :=
    hP.left.left.left.left.left.left.left.right.single
  have hEx : P.funs[a + 2]? = some (extE (a + 15) (a + 16) (a + 11)) :=
    hP.left.left.left.left.left.left.right.single
  have hF : P.HasAt (a + 3) (findFuns (a + 3) (a + 6)) := hP.left.left.left.left.left.right
  have hTs : P.funs[a + 6]? = some (isoTestE (a + 7) (a + 15)) :=
    hP.left.left.left.left.right.single
  have hAny : P.HasAt (a + 7) (anyFuns (a + 7) (a + 7 + 3)) := hP.left.left.left.right
  have hEq : P.funs[a + 7 + 3]? = some chkTestE := hP.left.left.right.single
  have hU : P.HasAt (a + 11) (tabFuns (a + 11) updE) := hP.left.right
  have hRi : P.HasAt (a + 15) (riFuns (a + 15) fd j) := hP.right
  have hLv : P.HasAt (a + 16) (levFuns (a + 16)) := hRi.left.left.left.right
  have hn : 0 < n := hS.pos
  have h0 := WB_ge n
  have hk := hS.k_le
  have hlk := le_kB n
  set v : Fin n := ⟨i, hi⟩ with hv
  have wc := riCtx_wt hS X Y
  have wacc := isoInv_wt hI
  have wi : (Val.nat i).wt ≤ WB n := nat_wt (by omega)
  obtain ⟨p, ok, rfl, hp, hok⟩ := hI
  have hok1 : ok ≤ 1 := by rcases hok with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  set acc := Val.list [encFun fun u => optN n (p u), .nat ok] with hacc
  set A := Val.list [riCtx D X Y, .nat i, acc] with hA
  have wA : A.wt ≤ 3 * (2 * (9 * (2 * WB n + 1) + 4 + (2 * (2 * WB n + 1) + 4) + WB n) + 1) + 4 :=
    wt_lit _ (by
      simp only [hA, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega)
  set T := isoStepT h S n with hT
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, isoStepT]; omega
  have hTs' : isoSrchC h S n + 1000 * WB n ≤ T := le_rfl
  have ga : ∀ {k : ℕ} {x : Val}, [riCtx D X Y, .nat i, acc][k]? = some x → k ≤ 2 →
      Lv P [A] T (arg k) x 1 := fun {k x} hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ k, k ≤ 8 → Lv P [A] T (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have g0 := Lv.get (vs := [encFun fun u => optN n (p u), .nat ok]) (ga (k := 2) rfl (by omega))
    (n9 0 (by omega)) rfl
  have g1 := Lv.get (vs := [encFun fun u => optN n (p u), .nat ok]) (ga (k := 2) rfl (by omega))
    (n9 1 (by omega)) rfl
  have gn := Lv.get (vs := [adjVal X, adjVal Y, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (ga (k := 0) rfl (by omega))
      (n9 2 (by omega)) rfl
  have av : Lv P [A] T (arg 1) (.nat (v : ℕ)) 1 := ga (k := 1) rfl (by omega)
  have keep : ∀ (m : ℕ) (Q : Val → ℕ → Prop), (∀ c', c' ≤ m * T → Q acc c') →
      Lv P [A] T (arg 2) acc m → EvalAll P [A] (arg 2) Q := fun m Q hq ha => Det.post ha hq
  refine FunAll.intro hM ((giIte_lv (R := fun w => IsoInv X Y (i + 1) w ∧ w.wt ≤ T)
    (K := 9000000 * T) g1 (fun hx => ?_) fun hx => ?_).mono fun w cb hw => ⟨hw.1.1, ?_⟩)
  rotate_left 2
  · have := hw.2
    simp only [isoStepC]
    omega
  · -- `ok = 1`
    have hok' : ok = 1 := by omega
    rcases hok with ⟨-, hlow, hag⟩ | ⟨h0', -⟩
    swap
    · omega
    have hpv := optN_le (p v)
    have cc := Lv.arith (op := .lt) (z := if optN n (p v) < n then 1 else 0) (Lv.tget g0 av) gn rfl
      (by split <;> omega)
    refine (giIte_lv (R := fun w => IsoInv X Y (i + 1) w ∧ w.wt ≤ T) (K := 8000000 * T) cc
      (fun hx => ?_) fun hx => ?_).mono fun w cb hw => ⟨hw.1, ?_⟩
    rotate_left 2
    · have := hw.2
      have := g1.wt_lt
      omega
    · -- `v` is already mapped
      have hpv' : p v ≠ none := by
        intro he
        rw [he] at hx
        simp [optN] at hx
      refine Det.post (ga (k := 2) rfl (by omega)) fun c' hc' => ⟨⟨⟨p, ok, rfl, hp, Or.inl
        ⟨hok', fun u hu => ?_, hag⟩⟩, by omega⟩, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
        · exact hlow u hu
        · have : u = v := Fin.ext hu
          rw [this]
          exact hpv'
      · have := cc.wt_lt
        omega
    · -- `v` is not mapped: search for an image
      have hpv' : p v = none := by
        by_contra hne
        rw [if_pos (show optN n (p v) < n by
          obtain ⟨x, hx'⟩ := Option.ne_none_iff_exists'.1 hne
          rw [hx']
          exact x.isLt)] at hx
        exact absurd hx (by norm_num)
      have hsr := search_spec h hSr hF hEx hTs hAny hEq hRi hLv hU hj hSol hS X Y dX dY p v
      have cA := Lv.mk3 (ga (k := 0) rfl (by omega)) g0 av (by omega)
      have hSC : isoSrchC h S n ≤ T := by omega
      refine (giCall_lv (R := fun w => IsoInv X Y (i + 1) w ∧ w.wt ≤ T) (K := 7000000 * T) cA
        (hsr.wt_lt.mono fun out c ho => ⟨⟨?_, by have := ho.2; omega⟩, ?_⟩)).mono
        fun w cb hw => ⟨hw.1, by have := hw.2; have := cc.wt_lt; omega⟩
      · rcases ho.1.1 with ⟨w, τ, hq, hτ, rfl⟩ | ⟨hno, rfl⟩
        · have hw : ∀ u, p u ≠ some w := fun u hu => hq.1 ⟨u, by show optN n (p u) = w; rw [hu]; rfl⟩
          refine ⟨addComp X p v τ, 1, rfl, hp.extend hpv' hw hτ, Or.inl ⟨rfl, fun u hu => ?_,
            fun hg => ?_⟩⟩
          · by_cases hr : X.Reachable v u
            · rw [addComp_new hr]
              simp
            · rw [addComp_old hr]
              rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
              · exact hlow u hu
              · exact absurd (by rw [show u = v from Fin.ext hu]) hr
          · obtain ⟨g, hg1, hg2⟩ := hag hg
            exact Agree.extend hp hg2 hg1 hpv' hw hτ
        · refine ⟨p, 0, rfl, hp, Or.inr ⟨rfl, fun hg => ?_⟩⟩
          obtain ⟨g, hg1, hg2⟩ := hag hg
          refine hno (g v) ⟨fun ⟨u, hu⟩ => hg2.free hpv' u ?_, g, isRooted_of_iso hg1 v⟩
          exact optN_eq_val.1 hu
      · have := ho.1.2
        have := ho.2
        omega
  · -- `ok = 0`
    have hok' : ok = 0 := hx
    subst hok'
    have hno : ¬∃ g, IsoP X Y g := by
      rcases hok with ⟨h1, -⟩ | ⟨-, h2⟩
      · omega
      · exact h2
    refine Det.post (ga (k := 2) rfl (by omega)) fun c' hc' =>
      ⟨⟨⟨p, 0, rfl, hp, Or.inr ⟨rfl, hno⟩⟩, by omega⟩, ?_⟩
    have := g1.wt_lt
    omega

/-- The loop over points. -/
def isoFuns (b fd j : ℕ) : List Expr :=
  iterFuns b (b + 3) ++ isoStepFuns (b + 3) fd j

/-- The cost of the loop over points. -/
noncomputable def isoLC (h : Membership) (S n : ℕ) : ℕ :=
  n * isoStepC h S n + loopModK * (n + 1) * (300 * WB n + n + 1)

/-- The start of the loop: nothing mapped. -/
def isoAcc0 (n : ℕ) : Val := .list [encFun fun _ : Fin n => n, .nat 1]

/-- **The loop over points.** -/
theorem iso_spec {P : Program} {b fd j S : ℕ} (h : Membership)
    (hP : P.HasAt b (isoFuns b fd j)) (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : SolverAt P fd D (n * D * (n * D)) S) (hS : Sz n D) (X Y : SimpleGraph (Fin n))
    (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U Y) u).length ≤ D) :
    FunAll P b (.list [riCtx D X Y, .nat n, isoAcc0 n]) fun out cost =>
      IsoInv X Y n out ∧ cost ≤ isoLC h S n := by
  have hIt : P.HasAt b (iterFuns b (b + 3)) := hP.left
  have hSt : P.HasAt (b + 3) (isoStepFuns (b + 3) fd j) := hP.right
  have h0 : IsoInv X Y 0 (isoAcc0 n) := ⟨fun _ => none, 1, rfl, partIso_none,
    Or.inl ⟨rfl, fun u hu => absurd hu (by omega), fun ⟨g, hg⟩ => ⟨g, hg, fun u a h => by cases h⟩⟩⟩
  have hit := iter_spec (c := riCtx D X Y) (k := n) (acc0 := isoAcc0 n) hIt (Inv := IsoInv X Y)
    (M := 2 * (2 * WB n + 1) + 4) (B := fun _ => isoStepC h S n) h0 (fun i acc hi hI => isoInv_wt hI)
    (fun i acc hi hI => isoStep_spec h hSt hj hSol hS X Y dX dY hi hI)
  refine FunAll.mono hit fun out c hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  have wa := isoInv_wt h0
  have h0 := WB_ge n
  have wc := riCtx_wt hS X Y
  have wk : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  have w3 : (Val.list [riCtx D X Y, .nat n, isoAcc0 n]).wt ≤
      3 * (2 * (9 * (2 * WB n + 1) + 4 + (2 * (2 * WB n + 1) + 4) + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  have e2 : loopModK * (n + 1) * ((Val.list [riCtx D X Y, .nat n, isoAcc0 n]).wt + n +
      (2 * (2 * WB n + 1) + 4) + 1) ≤ loopModK * (n + 1) * (300 * WB n + n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [isoLC]
  omega

/-- What the loop over points gives at the end. -/
theorem isoInv_final {X Y : SimpleGraph (Fin n)} {out : Val} (h : IsoInv X Y n out) :
    (∃ σ : X ≃g Y, out = .list [encPerm σ.toEquiv, .nat 1]) ∨ (∃ t : Val, out = .list [t, .nat 0]) ∧
      IsEmpty (X ≃g Y) := by
  obtain ⟨p, ok, rfl, hp, ⟨rfl, hall, -⟩ | ⟨rfl, hno⟩⟩ := h
  · have hs : ∀ u, ∃ a, p u = some a := fun u => Option.ne_none_iff_exists'.1 (hall u u.isLt)
    choose t ht using hs
    obtain ⟨σ, hσ⟩ := hp.total ht
    refine Or.inl ⟨σ, ?_⟩
    rw [encPerm_eq_encFun]
    congr 3
    funext u
    rw [ht u]
    simp [optN, hσ u]
  · refine Or.inr ⟨⟨_, rfl⟩, ⟨fun σ => hno ⟨σ.toEquiv, fun a b => σ.map_rel_iff.symm⟩⟩⟩

end GI.Degree
