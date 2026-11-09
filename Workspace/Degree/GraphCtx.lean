module

public import Workspace.Degree.GraphOut

/-!
# The context of the loops

From the largest degree `m`, the bound `D = m + 6`, the sizes `n D` and `(n D)²`, and the two
contexts `riCtx D X X` and `riCtx D X Y` of the loops.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- A list of nine values. -/
def mk9 (a b c d e f g h i : Expr) : Expr :=
  .snoc (.snoc (.snoc (.snoc (.snoc (mk4 a b c d) e) f) g) h) i

theorem Lv.mk9 {P : Program} {env : List Val} {T M : ℕ} {a b c d e f g h i : Expr}
    {xa xb xc xd xe xf xg xh xi : Val} {ma mb mc md me mf mg mh mi : ℕ}
    (ha : Lv P env T a xa ma) (hb : Lv P env T b xb mb) (hc : Lv P env T c xc mc)
    (hd : Lv P env T d xd md) (he : Lv P env T e xe me) (hf : Lv P env T f xf mf)
    (hg : Lv P env T g xg mg) (hh : Lv P env T h xh mh) (hi : Lv P env T i xi mi) (hT : 5 ≤ T)
    (hM : ma ≤ M ∧ mb ≤ M ∧ mc ≤ M ∧ md ≤ M ∧ me ≤ M ∧ mf ≤ M ∧ mg ≤ M ∧ mh ≤ M ∧ mi ≤ M) :
    Lv P env T (mk9 a b c d e f g h i) (.list [xa, xb, xc, xd, xe, xf, xg, xh, xi])
      (100000 * M + 100000) := by
  have := Lv.snoc (Lv.snoc (Lv.snoc (Lv.snoc (Lv.snoc (Lv.mk4 ha hb hc hd hT) he (by omega)) hf
    (by omega)) hg (by omega)) hh (by omega)) hi (by omega)
  exact Lv.mono this (by omega)

/-- The context, on `[[n, adj X, adj Y], ids n, m]`. -/
def ctxE (rng : ℕ) : Expr :=
  let nn := Expr.get (arg 0) (.nat 0)
  let aX := Expr.get (arg 0) (.nat 1)
  let aY := Expr.get (arg 0) (.nat 2)
  .letE (.arith .add (arg 2) (.nat 6))
  (.letE (.arith .mul nn (.var 1))
  (.letE (.arith .mul (.var 2) (.var 2))
  (.letE (.call rng (.var 2))
  (.letE (.call rng (.var 3))
    (mk2 (mk9 aX aX nn (arg 1) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
      (mk9 aX aY nn (arg 1) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)))))))

/-- The cost of a range. -/
def rngC (n : ℕ) : ℕ := loopModK * (kB n + n + 1) * (3 * WB n + kB n + n + 1)

theorem rng_spec {P : Program} {r : ℕ} (hR : P.HasAt r (rangeFuns r)) {m : ℕ}
    (hm : m ≤ kB n + n) : FunDet P r (.nat m) (ids m) (rngC n) := by
  have h0 := WB_ge n
  refine FunAll.mono (range_spec hR m) fun w cw hw => ⟨?_, ?_⟩
  · rw [hw.1, ← encFun_id]
  · have hc := hw.2
    rw [hw.1, ← encFun_id] at hc
    have w1 : (Val.nat m).wt ≤ WB n := nat_wt (by omega)
    have w2 : (encFun fun i : Fin m => (i : ℕ)).wt ≤ WB n := table_wt hm fun i => i.isLt.le
    have e : loopModK * (m + 1) * ((Val.nat m).wt + m + (encFun fun i : Fin m => (i : ℕ)).wt + 1) ≤
        loopModK * (kB n + n + 1) * (3 * WB n + kB n + n + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    simp only [rngC]
    omega

/-- The budget of the context. -/
def ctxT (n : ℕ) : ℕ := rngC n + 1000 * WB n

/-- The input of the program, decoded. -/
noncomputable def inVal (X Y : SimpleGraph (Fin n)) : Val := .list [.nat n, adjVal X, adjVal Y]

theorem inVal_wt (X Y : SimpleGraph (Fin n)) : (inVal X Y).wt ≤ 3 * (2 * WB n + 1) + 4 := by
  have h0 := WB_ge n
  have wX := adjVal_wt (n := n) X
  have wY := adjVal_wt (n := n) Y
  have wn : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
  exact wt_lit _ (by
    simp only [inVal, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)

set_option maxHeartbeats 4000000 in
theorem ctx_spec {P : Program} {a r : ℕ} (hM : P.funs[a]? = some (ctxE r))
    (hR : P.HasAt r (rangeFuns r)) (X Y : SimpleGraph (Fin n)) {m : ℕ} (hm : m ≤ n) :
    FunDet P a (.list [inVal X Y, ids n, .nat m])
      (.list [riCtx (m + 6) X X, riCtx (m + 6) X Y]) (1000000000 * ctxT n) := by
  have h0 := WB_ge n
  have hlk := le_kB n
  have wI := inVal_wt X Y
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wm : (Val.nat m).wt ≤ WB n := nat_wt (by omega)
  set D := m + 6 with hD
  have hDn : D ≤ n + 6 := by omega
  have hnD : n * D ≤ n * (n + 6) := Nat.mul_le_mul_left _ hDn
  have hk : n * D * (n * D) ≤ kB n := by
    have := Nat.mul_le_mul hnD hnD
    simpa [kB, sq] using this
  have hnk : n * D ≤ kB n := by
    rcases Nat.eq_zero_or_pos (n * D) with h | h
    · omega
    · exact le_trans (Nat.le_mul_of_pos_right _ h) hk
  have wD : (Val.nat D).wt ≤ WB n := nat_wt (by omega)
  have wnD : (Val.nat (n * D)).wt ≤ WB n := nat_wt (by omega)
  have wk : (Val.nat (n * D * (n * D))).wt ≤ WB n := nat_wt (by omega)
  have wi1 : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wi2 : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  set A := Val.list [inVal X Y, ids n, .nat m] with hA
  have wA : A.wt ≤ 3 * (2 * (3 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [hA, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  set T := ctxT n with hT
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, ctxT]; omega
  have hTW : 100 * WB n ≤ T := by simp only [hT, ctxT]; omega
  have hTR : rngC n ≤ T := by simp only [hT, ctxT]; omega
  have ga : ∀ rest {k : ℕ} {x : Val}, [inVal X Y, ids n, .nat m][k]? = some x → k ≤ 2 →
      Lv P (A :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gI : ∀ rest (k : ℕ) {x : Val}, [Val.nat n, adjVal X, adjVal Y][k]? = some x → k ≤ 2 →
      Lv P (A :: rest) T (.get (arg 0) (.nat k)) x (2 * 1 + 1 + 1) := fun rest k x hx hk =>
    Lv.get (vs := [.nat n, adjVal X, adjVal Y]) (ga rest (k := 0) rfl (by omega)) (n9 _ k (by omega)) hx
  have v1 := Lv.arith (op := .add) (z := D) (ga [] (k := 2) rfl (by omega)) (n9 [A] 6 (by omega))
    rfl (by omega)
  have v2 := Lv.arith (op := .mul) (z := n * D) (gI [.nat D] 0 rfl (by omega))
    (Lv.var (env := [A, .nat D]) (i := 1) (v := .nat D) rfl (by omega)) rfl (by omega)
  have v3 := Lv.arith (op := .mul) (z := n * D * (n * D))
    (Lv.var (P := P) (T := T) (env := [A, .nat D, .nat (n * D)]) (i := 2) (v := .nat (n * D)) rfl (by omega))
    (Lv.var (P := P) (T := T) (env := [A, .nat D, .nat (n * D)]) (i := 2) (v := .nat (n * D)) rfl (by omega))
    rfl (by omega)
  have v4 := Lv.call (Lv.var (P := P) (T := T) (env := [A, .nat D, .nat (n * D), .nat (n * D * (n * D))]) (i := 2)
    (v := .nat (n * D)) rfl (by omega)) (rng_spec hR (n := n) (m := n * D) (by omega)) hTR
  have v5 := Lv.call (Lv.var (P := P) (T := T) (env := [A, .nat D, .nat (n * D), .nat (n * D * (n * D)),
    ids (n * D)]) (i := 3) (v := .nat (n * D * (n * D))) rfl (by omega))
    (rng_spec hR (n := n) (m := n * D * (n * D)) (by omega)) hTR
  set E := [A, .nat D, .nat (n * D), .nat (n * D * (n * D)), ids (n * D),
    ids (n * D * (n * D))] with hE
  have vv : ∀ (i : ℕ) {x : Val}, E[i]? = some x → x.wt ≤ WB n → Lv P E T (.var i) x 1 :=
    fun i x hx hw => Lv.var hx (by omega)
  have c1 := Lv.mk9 (M := 10) (gI _ 1 rfl (by omega)) (gI _ 1 rfl (by omega)) (gI _ 0 rfl (by omega))
    (ga _ (k := 1) rfl (by omega)) (vv 1 rfl wD) (vv 2 rfl wnD) (vv 3 rfl wk) (vv 4 rfl wi1)
    (vv 5 rfl wi2) (by omega) (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num)
  have c2 := Lv.mk9 (M := 10) (gI _ 1 rfl (by omega)) (gI _ 2 rfl (by omega)) (gI _ 0 rfl (by omega))
    (ga _ (k := 1) rfl (by omega)) (vv 1 rfl wD) (vv 2 rfl wnD) (vv 3 rfl wk) (vv 4 rfl wi1)
    (vv 5 rfl wi2) (by omega) (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num)
  have c := Lv.mk2 c1 c2 (by omega)
  exact funDet_of_lv hM (Lv.mono (e := ctxE r)
    (Lv.letE v1 (Lv.letE v2 (Lv.letE v3 (Lv.letE v4 (Lv.letE v5 c))))) (by norm_num))

end GI.Degree
