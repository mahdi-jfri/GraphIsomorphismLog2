module

public import Workspace.Degree.GraphIso

/-!
# Degrees

The bound `D` of the program is six plus the largest degree in `X` and `Y`. This file gives the
facts about degrees that the program needs: the out-neighbours of a point are among its neighbours,
and the degree is the one of `DegreeAtMost`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

open Classical in
/-- The degree of `u`, as the program counts it. -/
noncomputable def degL (X : SimpleGraph (Fin n)) (u : Fin n) : ℕ :=
  ((List.finRange n).filter fun w => decide (X.Adj u w)).length

open Classical in
theorem lenFilter_card (p : Fin n → Prop) :
    ((List.finRange n).filter fun w => decide (p w)).length = Fintype.card {w // p w} := by
  rw [Fintype.card_subtype, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),
    List.toFinset_filter, List.toFinset_finRange]
  simp

theorem degL_le (X : SimpleGraph (Fin n)) (u : Fin n) : degL X u ≤ n := by
  unfold degL
  exact (List.length_filter_le _ _).trans (by simp)

theorem degL_eq_ncard (X : SimpleGraph (Fin n)) (u : Fin n) : degL X u = (X.neighborSet u).ncard := by
  classical
  rw [degL, lenFilter_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun w => Iff.rfl)

theorem degL_pull (U : Perm (Fin n)) (Y : SimpleGraph (Fin n)) (u : Fin n) :
    degL (pull U Y) u = degL Y (U u) := by
  classical
  rw [degL, degL, lenFilter_card, lenFilter_card]
  exact Fintype.card_congr (U.subtypeEquiv fun w => Iff.rfl)

theorem fwd_le_degL (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) (u : Fin n) :
    (fwd ℓ X u).length ≤ degL X u := by
  classical
  unfold fwd degL
  refine (List.monotone_filter_right _ fun w hw => ?_).length_le
  simp only [decide_eq_true_eq] at hw ⊢
  exact hw.1

/-! ### The program -/

open Classical in
/-- A row of the adjacency matrix. -/
noncomputable def rowF (X : SimpleGraph (Fin n)) (u : Fin n) : Fin n → ℕ :=
  fun j => if X.Adj u j then 1 else 0

theorem adjVal_rows (X : SimpleGraph (Fin n)) :
    adjVal X = .list ((List.finRange n).map fun i => encFun (rowF X i)) := rfl

/-- The test of the count, on `[row, j]`. -/
def degTestE : Expr := .arith .eq (.get (arg 0) (arg 1)) (.nat 1)

/-- A budget for small values. -/
def dgT (n : ℕ) : ℕ := 1000 * WB n

theorem degTest_lv {P : Program} (X : SimpleGraph (Fin n)) (u z : Fin n) :
    Lv P [.list [encFun (rowF X u), .nat z]] (dgT n) degTestE
      (boolVal (@decide (X.Adj u z) (Classical.propDecidable _))) 100 := by
  classical
  have h0 := WB_ge n
  have hr : (encFun (rowF X u)).wt ≤ WB n := table_wt (by omega) fun j => by
    have := z.isLt
    simp only [rowF]
    split <;> omega
  have wz : (Val.nat z).wt ≤ WB n := fin_wt (by omega) z
  have w2 : (Val.list [encFun (rowF X u), .nat z]).wt ≤ 2 * (2 * WB n + 1) + 4 :=
    wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> omega)
  have hT : dgT n = 1000 * WB n := rfl
  have a0 : Lv P [.list [encFun (rowF X u), .nat z]] (dgT n) (arg 0) (encFun (rowF X u)) 1 :=
    Lv.arg rfl (by omega)
  have a1 : Lv P [.list [encFun (rowF X u), .nat z]] (dgT n) (arg 1) (.nat z) 1 :=
    Lv.arg rfl (by omega)
  have e1 := Lv.arith (op := .eq) (z := if X.Adj u z then 1 else 0) (Lv.tget a0 a1)
    (Lv.nat 1 (by omega)) (by simp only [BinOp.eval, rowF]; split_ifs <;> simp_all)
    (by split <;> omega)
  rw [boolVal_ite]
  exact Lv.mono (e := degTestE) e1 (by norm_num)

/-- The step of the loop for the largest degree, on `[[adj X, adj Y, ids], i, m]`. -/
def degStepE (fl : ℕ) : Expr :=
  let cnt (k : ℕ) : Expr :=
    .length (.call fl (mk2 (.get (.get (arg 0) (.nat k)) (arg 1)) (.get (arg 0) (.nat 2))))
  .letE (cnt 0) (.letE (.ite (.arith .lt (arg 2) (.var 1)) (.var 1) (arg 2))
    (.letE (cnt 1) (.ite (.arith .lt (.var 2) (.var 3)) (.var 3) (.var 2))))

theorem max_lv {P : Program} {env : List Val} {T : ℕ} {a b : Expr} {x y ma mb : ℕ}
    (ha : Lv P env T a (.nat x) ma) (hb : Lv P env T b (.nat y) mb) (hT : 4 ≤ T) :
    Lv P env T (.ite (.arith .lt a b) b a) (.nat (max x y)) (ma + mb + 1 + 2 * (ma + mb)) := by
  by_cases h : x < y
  · have c := Lv.arith (op := .lt) (z := 1) ha hb (by simp [BinOp.eval, h]) (by omega)
    rw [max_eq_right h.le]
    exact Lv.mono (Lv.ite_pos c one_ne_zero hb) (by omega)
  · have c := Lv.arith (op := .lt) (z := 0) ha hb (by simp [BinOp.eval, h]) (by omega)
    rw [max_eq_left (by omega)]
    exact Lv.mono (Lv.ite_zero c ha) (by omega)

/-- The cost of a count. -/
def filtC (n : ℕ) : ℕ := n * (100 * dgT n) + loopModK * (n + 1) * (100 * WB n)

/-- The budget of the step. -/
def dgStepT (n : ℕ) : ℕ := filtC n + dgT n

/-- The context of the loop. -/
noncomputable def degCtx (X Y : SimpleGraph (Fin n)) : Val := .list [adjVal X, adjVal Y, ids n]

theorem degCtx_wt (X Y : SimpleGraph (Fin n)) : (degCtx X Y).wt ≤ 3 * (2 * WB n + 1) + 4 := by
  have h0 := WB_ge n
  have wX := adjVal_wt (n := n) X
  have wY := adjVal_wt (n := n) Y
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)

set_option maxHeartbeats 4000000 in
theorem count_lv {P : Program} {fl : ℕ} (hFl : P.HasAt fl (filterFuns fl (fl + 3)))
    (hTs : P.funs[fl + 3]? = some degTestE) (Z : SimpleGraph (Fin n)) (u : Fin n)
    {env : List Val} {T ma mb : ℕ} {r i : Expr}
    (hr : Lv P env T r (encFun (rowF Z u)) ma) (hi : Lv P env T i (ids n) mb)
    (hT : dgStepT n ≤ T) :
    Lv P env T (.length (.call fl (mk2 r i))) (.nat (degL Z u))
      (2 * (2 * (2 * 1 + 3 * ma + 1) + 3 * mb + 1 + 2) + 1) := by
  classical
  have h0 := WB_ge n
  have hlB := levB_le_WB n
  have hrw : (encFun (rowF Z u)).wt ≤ WB n := table_wt (by omega) fun j => by
    have := u.isLt
    simp only [rowF]
    split <;> omega
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wf := flist_levB ((List.finRange n).filter fun w => decide (Z.Adj u w))
    (by simpa using List.length_filter_le (fun w => decide (Z.Adj u w)) (List.finRange n))
  have w2 : (Val.list [encFun (rowF Z u), ids n]).wt ≤ 2 * (2 * WB n + 1) + 4 :=
    wt_lit _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> omega)
  have hF := filterFin_spec (c := encFun (rowF Z u)) hFl (fun w => Z.Adj u w) (B := 100 * dgT n)
    (W := 100 * WB n) (fun z => funDet_of_lv hTs (degTest_lv Z u z)) (by omega)
  have c := Lv.length (Lv.call (Lv.mk2 hr hi (by simp only [dgStepT, dgT] at hT; omega)) hF
    (by simp only [dgStepT, filtC] at hT; omega)) (by simp only [dgStepT, dgT] at hT; omega)
  have e : (((List.finRange n).filter fun w => decide (Z.Adj u w)).map
      fun z : Fin n => Val.nat (z : ℕ)).length = degL Z u := by
    simp [degL]
  rw [← e]
  exact c

set_option maxHeartbeats 4000000 in
theorem degStep_spec {P : Program} {a : ℕ} (hM : P.funs[a]? = some (degStepE (a + 1)))
    (hFl : P.HasAt (a + 1) (filterFuns (a + 1) (a + 1 + 3)))
    (hTs : P.funs[a + 1 + 3]? = some degTestE) (X Y : SimpleGraph (Fin n)) {i m : ℕ} (hi : i < n)
    (hm : m ≤ n) :
    FunDet P a (.list [degCtx X Y, .nat i, .nat m])
      (.nat (max (max m (degL X ⟨i, hi⟩)) (degL Y ⟨i, hi⟩))) (100000 * dgStepT n) := by
  classical
  set u : Fin n := ⟨i, hi⟩ with hu
  have h0 := WB_ge n
  have wc := degCtx_wt X Y
  have wi : (Val.nat i).wt ≤ WB n := nat_wt (by omega)
  have wm : (Val.nat m).wt ≤ WB n := nat_wt (by omega)
  set A := Val.list [degCtx X Y, .nat i, .nat m] with hA
  have wA : A.wt ≤ 3 * (2 * (3 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
    simp only [hA, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  set T := dgStepT n with hT
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, dgStepT, dgT]; omega
  have hTW : 100 * WB n ≤ T := by simp only [hT, dgStepT, dgT]; omega
  have ga : ∀ rest {k : ℕ} {x : Val}, [degCtx X Y, .nat i, .nat m][k]? = some x → k ≤ 2 →
      Lv P (A :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gc : ∀ rest (k : ℕ) {x : Val}, [adjVal X, adjVal Y, ids n][k]? = some x → k ≤ 2 →
      Lv P (A :: rest) T (.get (arg 0) (.nat k)) x _ := fun rest k x hx hk =>
    Lv.get (vs := [adjVal X, adjVal Y, ids n]) (ga rest (k := 0) rfl (by omega)) (n9 _ k (by omega)) hx
  have row : ∀ rest (k : ℕ) (Z : SimpleGraph (Fin n)),
      [adjVal X, adjVal Y, ids n][k]? = some (adjVal Z) → k ≤ 2 →
      Lv P (A :: rest) T (.get (.get (arg 0) (.nat k)) (arg 1)) (encFun (rowF Z u)) _ :=
    fun rest k Z hx hk => Lv.get (vs := (List.finRange n).map fun i => encFun (rowF Z i))
      (gc rest k hx hk) (ga rest (k := 1) rfl (by omega)) (listFin_get _ u)
  have cX := count_lv hFl hTs X u (row [] 0 X rfl (by omega)) (gc [] 2 rfl (by omega)) le_rfl
  have m1 := max_lv (ga [.nat (degL X u)] (k := 2) rfl (by omega))
    (Lv.var (env := [A, .nat (degL X u)]) (i := 1) rfl (by
      have := nat_wt (n := n) (k := degL X u) (by have := degL_le X u; omega)
      omega)) (by omega)
  have cY := count_lv hFl hTs Y u (row [.nat (degL X u), .nat (max m (degL X u))] 1 Y rfl
    (by omega)) (gc [.nat (degL X u), .nat (max m (degL X u))] 2 rfl (by omega)) le_rfl
  have hXl := degL_le X u
  have hYl := degL_le Y u
  have wmx : (Val.nat (max m (degL X u))).wt ≤ WB n := nat_wt (by omega)
  have wmx' : (Val.nat (max m (degL X u))).wt + 1 ≤ T := by omega
  have wdy : (Val.nat (degL Y u)).wt ≤ WB n := nat_wt (by omega)
  have m2 := max_lv (P := P) (Lv.var (env := [A, .nat (degL X u), .nat (max m (degL X u)),
      .nat (degL Y u)]) (i := 2) (v := .nat (max m (degL X u))) rfl wmx')
    (Lv.var (env := [A, .nat (degL X u), .nat (max m (degL X u)), .nat (degL Y u)]) (i := 3)
      (v := .nat (degL Y u)) rfl (by omega)) (by omega)
  exact funDet_of_lv hM (Lv.mono (Lv.letE cX (Lv.letE m1 (Lv.letE cY m2))) (by norm_num))

/-- The invariant of the loop for the largest degree. -/
def DegInv (X Y : SimpleGraph (Fin n)) (i : ℕ) (acc : Val) : Prop :=
  ∃ m, acc = .nat m ∧ m ≤ n ∧ (∀ u : Fin n, (u : ℕ) < i → degL X u ≤ m ∧ degL Y u ≤ m) ∧
    ∀ d, (∀ u, degL X u ≤ d ∧ degL Y u ≤ d) → m ≤ d

/-- The loop for the largest degree. -/
def maxDegFuns (b : ℕ) : List Expr :=
  iterFuns b (b + 3) ++ [degStepE (b + 4)] ++ filterFuns (b + 4) (b + 7) ++ [degTestE]

/-- The cost of the loop. -/
def degLC (n : ℕ) : ℕ := n * (100000 * dgStepT n) + loopModK * (n + 1) * (100 * WB n + n + 1)

/-- **The largest degree.** -/
theorem deg_spec {P : Program} {b : ℕ} (hP : P.HasAt b (maxDegFuns b)) (X Y : SimpleGraph (Fin n)) :
    FunAll P b (.list [degCtx X Y, .nat n, .nat 0]) fun out cost =>
      (∃ m, out = .nat m ∧ m ≤ n ∧ (∀ u, degL X u ≤ m ∧ degL Y u ≤ m) ∧
        ∀ d, (∀ u, degL X u ≤ d ∧ degL Y u ≤ d) → m ≤ d) ∧ cost ≤ degLC n := by
  have hIt : P.HasAt b (iterFuns b (b + 3)) := hP.left.left.left
  have hM : P.funs[b + 3]? = some (degStepE (b + 3 + 1)) := hP.left.left.right.single
  have hFl : P.HasAt (b + 3 + 1) (filterFuns (b + 3 + 1) (b + 3 + 1 + 3)) := hP.left.right
  have hTs : P.funs[b + 3 + 1 + 3]? = some degTestE := hP.right.single
  have h0 : DegInv X Y 0 (.nat 0) :=
    ⟨0, rfl, by omega, fun u hu => absurd hu (by omega), fun d _ => by omega⟩
  have hWB := WB_ge n
  have hit := iter_spec (c := degCtx X Y) (k := n) (acc0 := .nat 0) hIt (Inv := DegInv X Y)
    (M := WB n) (B := fun _ => 100000 * dgStepT n) h0
    (fun i acc hi hI => by
      obtain ⟨m, rfl, hm, -⟩ := hI
      exact nat_wt (by omega))
    (fun i acc hi hI => by
      obtain ⟨m, rfl, hm, hlow, hup⟩ := hI
      refine FunAll.mono (degStep_spec hM hFl hTs X Y hi hm) fun w c hw => ⟨?_, hw.2⟩
      obtain ⟨rfl, -⟩ := hw
      refine ⟨_, rfl, ?_, fun u hu => ?_, fun d hd => ?_⟩
      · have := degL_le X ⟨i, hi⟩
        have := degL_le Y ⟨i, hi⟩
        omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
        · have := hlow u hu
          omega
        · have e : u = ⟨i, hi⟩ := Fin.ext hu
          subst e
          omega
      · have := hup d hd
        have := hd ⟨i, hi⟩
        omega)
  refine FunAll.mono hit fun out c hw => ⟨?_, ?_⟩
  · obtain ⟨m, rfl, hm, hlow, hup⟩ := hw.1
    exact ⟨m, rfl, hm, fun u => hlow u u.isLt, hup⟩
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have wc := degCtx_wt X Y
    have wk : (Val.nat n).wt ≤ WB n := nat_wt (by omega)
    have w0 : (Val.nat 0).wt ≤ WB n := nat_wt (by omega)
    have w3 : (Val.list [degCtx X Y, .nat n, .nat 0]).wt ≤
        3 * (2 * (3 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega)
    have e2 : loopModK * (n + 1) * ((Val.list [degCtx X Y, .nat n, .nat 0]).wt + n + WB n + 1) ≤
        loopModK * (n + 1) * (100 * WB n + n + 1) := Nat.mul_le_mul_left _ (by omega)
    simp only [degLC]
    omega

end GI.Degree
