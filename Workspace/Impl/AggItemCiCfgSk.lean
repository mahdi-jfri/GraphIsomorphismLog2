import Workspace.Impl.AggItemCiCfgN

/-!
# The configuration query: the step program

The step `itcqSkF fB fal` on an item state `[kst, u]` (`kst = itcqKs X x₀ Y y₀ w`, `u` the
answer):
* if the answer is empty (`u = []`), there is no map of the fibers that keeps the colors and
  the branch has no overcoset: it returns `itcqEmp w` (`itcq_skF_emp`);
* if the outer color classes of `X` and `Y` cannot be aligned (the test `itcqAlF`, which
  compares the colors along the outer points by color), the branch has no overcoset either
  ("align those classes", Lemma A.12): it returns `itcqEmp w` (`itcq_skF_nal`);
* otherwise it calls `fB` (the program `itcqSbF`, `itcq_sbF_spec`), `itcq_skF_ne`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- The empty result of the step program, from the kept value. -/
def itcqEmpE : Expr := mk2 (.nat 0) (mk3 .nil .nil (.get (.get (.var 0) (.nat 0)) (.nat 0)))

/-- **The alignment test** on `[kst, u]`: whether the colors along the outer points by color
of `X` and of `Y` agree (`ItciAl X Y`). -/
def itcqAlF (fds fcm feq : ℕ) : Expr :=
  .call feq (mk2 (.call fcm (mk2 (itcqK 1) (.call fds (itcqK 1))))
    (.call fcm (mk2 (itcqK 2) (.call fds (itcqK 2)))))

/-- **The step program**: the empty result on an empty answer or on outer classes that cannot be
aligned, `fB` otherwise. -/
def itcqSkF (fB fal : ℕ) : Expr :=
  .ite (.length (.get (.var 0) (.nat 1)))
    (.ite (.call fal (.var 0)) (.call fB (.var 0)) itcqEmpE) itcqEmpE

/-- The cost bound of the alignment test. -/
def itcqAlC (M : ℕ) : ℕ := 2 * itcqDsC M + 2 * itcqCoC (20 * (M + 1) ^ 2) + 10 ^ 6 * (M + 1) ^ 3

/-- The cost bound of the step program. -/
def itcqSkC (M : ℕ) : ℕ := 20 * itcqSbC M + itcqAlC M + 1000 * (M + 1)

section Prog

variable {P : Program}

/-- **The step on an empty answer.** -/
theorem itcq_skF_emp {f fB fal : ℕ} (hf : P.funs[f]? = some (itcqSkF fB fal)) (X : PairCfg q) (x₀ : Fin q)
    (Y : PairCfg q) (y₀ : Fin q) (w : Val) {M : ℕ}
    (hM : (Val.list [itcqKs X x₀ Y y₀ w, .list []]).wt ≤ M) :
    FunDet P f (.list [itcqKs X x₀ Y y₀ w, .list []]) (itcqEmp w) (itcqSkC M) := by
  have hk : (itcqKs X x₀ Y y₀ w).wt < (Val.list [itcqKs X x₀ Y y₀ w, .list []]).wt :=
    wt_le_wt_list (List.mem_cons_self ..)
  have hk0 : w.wt < (itcqKs X x₀ Y y₀ w).wt := wt_le_wt_list (List.mem_cons_self ..)
  have hn : (Val.list []).wt < (Val.list [itcqKs X x₀ Y y₀ w, .list []]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have he : (itcqEmp w).wt ≤ 2 * (2 * (w.wt + 2 * (Val.list []).wt) + 7 + 2) + 6 := by
    have h1 := wt_list3_le (.list []) (.list []) w
    have h2 := wt_list2_le (.nat 0) (.list [.list [], .list [], w])
    have h3 := wt_nat_le 0
    unfold itcqEmp; omega
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * M + 40 := ⟨_, rfl⟩
  have v0 := StDC.var' (P := P) (env := [.list [itcqKs X x₀ Y y₀ w, .list []]]) (i := 0) rfl
    (W := W) (by omega)
  have g1 := StDC.get v0 (StDC.nat 1 (by omega)) (v := .list []) rfl (by omega)
  have ln := StDC.length g1 (vs := []) (by simp; omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := itcqKs X x₀ Y y₀ w) rfl (by omega)
  have g00 := StDC.get g0 (StDC.nat 0 (by omega)) (v := w) rfl (by omega)
  have h3 := wt_list3_le (.list []) (.list []) w
  have m3 := StDC.mk3 (StDC.nil (P := P) (by omega)) (StDC.nil (P := P) (by omega)) g00
    (by omega) (by omega)
  have m2 := StDC.mk2 (StDC.nat 0 (by omega)) m3 (by unfold itcqEmp at he; omega) (by omega)
  have it := StDC.ite (t := .ite (.call fal (.var 0)) (.call fB (.var 0)) itcqEmpE) (nt := 0)
    (Et := 0) ln (fun h => absurd rfl h) (fun _ => m2)
    (by unfold itcqEmp at he; omega)
  refine StDC.funDet hf it ?_
  unfold itcqSkC itcqSbC
  subst hW
  omega

/-- **The step on a nonempty answer, with aligned classes.** -/
theorem itcq_skF_ne {f fB fal : ℕ} (hf : P.funs[f]? = some (itcqSkF fB fal)) {kv x G v : Val}
    {M : ℕ} (hB : FunDet P fB (.list [kv, .list [x, G]]) v (itcqSbC M))
    (hal : FunDet P fal (.list [kv, .list [x, G]]) (boolVal true) (itcqAlC M))
    (hM : (Val.list [kv, .list [x, G]]).wt ≤ M) :
    FunDet P f (.list [kv, .list [x, G]]) v (itcqSkC M) := by
  have hn : (Val.list [x, G]).wt < (Val.list [kv, .list [x, G]]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hv := hB.wt_lt
  obtain ⟨W, hW⟩ : ∃ W, W = M + itcqSbC M + 10 := ⟨_, rfl⟩
  have v0 := StDC.var' (P := P) (env := [.list [kv, .list [x, G]]]) (i := 0) rfl
    (W := W) (by omega)
  have g1 := StDC.get v0 (StDC.nat 1 (by omega)) (v := .list [x, G]) rfl (by omega)
  have ln := StDC.length g1 (vs := [x, G]) (by simp; omega)
  have cl := StDC.call v0 hB (by omega)
  have ca := StDC.call v0 hal (by have := wt_boolVal_le true; omega)
  have it2 := StDC.ite (e := itcqEmpE) (ne := 0) (Ee := 0) ca (fun _ => cl)
    (fun h => absurd h (by simp)) (by omega)
  have it := StDC.ite (e := itcqEmpE) (ne := 0) (Ee := 0) ln (fun _ => it2)
    (fun h => absurd h (by simp)) (by omega)
  refine StDC.funDet hf it ?_
  unfold itcqSkC
  subst hW
  omega

/-- **The step on a nonempty answer, with classes that cannot be aligned.** -/
theorem itcq_skF_nal {f fB fal : ℕ} (hf : P.funs[f]? = some (itcqSkF fB fal)) (X : PairCfg q)
    (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val) {x G : Val} {M : ℕ}
    (hal : FunDet P fal (.list [itcqKs X x₀ Y y₀ w, .list [x, G]]) (boolVal false) (itcqAlC M))
    (hM : (Val.list [itcqKs X x₀ Y y₀ w, .list [x, G]]).wt ≤ M) :
    FunDet P f (.list [itcqKs X x₀ Y y₀ w, .list [x, G]]) (itcqEmp w) (itcqSkC M) := by
  have hk : (itcqKs X x₀ Y y₀ w).wt < (Val.list [itcqKs X x₀ Y y₀ w, .list [x, G]]).wt :=
    wt_le_wt_list (List.mem_cons_self ..)
  have hk0 : w.wt < (itcqKs X x₀ Y y₀ w).wt := wt_le_wt_list (List.mem_cons_self ..)
  have hn : (Val.list [x, G]).wt < (Val.list [itcqKs X x₀ Y y₀ w, .list [x, G]]).wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have he : (itcqEmp w).wt ≤ 2 * (2 * (w.wt + 2 * (Val.list []).wt) + 7 + 2) + 6 := by
    have h1 := wt_list3_le (.list []) (.list []) w
    have h2 := wt_list2_le (.nat 0) (.list [.list [], .list [], w])
    have h3 := wt_nat_le 0
    unfold itcqEmp; omega
  have hnil : (Val.list []).wt ≤ 4 := by simp [wt_list_eq]
  obtain ⟨W, hW⟩ : ∃ W, W = 20 * M + 40 := ⟨_, rfl⟩
  have v0 := StDC.var' (P := P) (env := [.list [itcqKs X x₀ Y y₀ w, .list [x, G]]]) (i := 0) rfl
    (W := W) (by omega)
  have g1 := StDC.get v0 (StDC.nat 1 (by omega)) (v := .list [x, G]) rfl (by omega)
  have ln := StDC.length g1 (vs := [x, G]) (by simp; omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := itcqKs X x₀ Y y₀ w) rfl (by omega)
  have g00 := StDC.get g0 (StDC.nat 0 (by omega)) (v := w) rfl (by omega)
  have m3 := StDC.mk3 (StDC.nil (P := P) (by omega)) (StDC.nil (P := P) (by omega)) g00
    (by have := wt_list3_le (.list []) (.list []) w; omega) (by omega)
  have m2 := StDC.mk2 (StDC.nat 0 (by omega)) m3 (by unfold itcqEmp at he; omega) (by omega)
  have ca := StDC.call v0 hal (by have := wt_boolVal_le false; omega)
  have it2 := StDC.ite (t := .call fB (.var 0)) (nt := 0) (Et := 0) ca
    (fun h => absurd h (by simp)) (fun _ => m2) (by unfold itcqEmp at he; omega)
  have it := StDC.ite (e := itcqEmpE) (ne := 0) (Ee := 0) ln (fun _ => it2)
    (fun h => absurd h (by simp)) (by unfold itcqEmp at he; omega)
  refine StDC.funDet hf it ?_
  unfold itcqSkC itcqAlC
  subst hW
  omega

/-- The colors along the outer points by color weigh at most `d (2 wt + 1) + 4`. -/
theorem itcq_cols_wt (Z : PairCfg q) (z₀ : Fin q) :
    (natList ((itciFo Z).map fun a => Z.col a a)).wt ≤
      (itciFo Z).length * (2 * (rcCertIn Z z₀).wt + 1) + 4 := by
  have h := wt_list_le_of (((itciFo Z).map fun a => Z.col a a).map Val.nat)
    (c := (rcCertIn Z z₀).wt) (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      exact ((st_wt_mem (List.mem_of_getElem? (encFun_getElem? (Z.col a) a))).trans
        (st_wt_mem (List.mem_of_getElem? (itcq_col_get Z a)))).trans
        (st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat (z₀ : ℕ)] by simp)))
  simp only [List.length_map] at h
  exact h

theorem itcq_alC_arith {M q d n C Ds Co B Wl : ℕ} (hq : q < M) (hd : d ≤ q) (hn : n ≤ 100)
    (hWl : Wl = 30 * (M + 1) ^ 2 + 100) (hB : B ≤ 20 * (M + 1) ^ 2)
    (hC : C ≤ n * (Wl + 1) + (Ds + Co + (Ds + Co) + loopModK * (d + 1) * (B + d + 4))) :
    C ≤ 2 * Ds + 2 * Co + 10 ^ 6 * (M + 1) ^ 3 := by
  unfold loopModK at hC
  have h1 : 1000 * (d + 1) * (B + d + 4) ≤ 1000 * ((M + 1) * (120 * (M + 1) ^ 2)) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) ?_)
    have : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have e1 : (M + 1) * (120 * (M + 1) ^ 2) = 120 * (M + 1) ^ 3 := by ring
  rw [e1] at h1
  have h2 : n * (Wl + 1) ≤ 100 * (131 * (M + 1) ^ 2) := Nat.mul_le_mul hn (by
    have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega)
  have h3 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have : (10 : ℕ) ^ 6 = 1000000 := by norm_num
  rw [this]
  omega

set_option maxHeartbeats 1000000 in
/-- **The alignment test**: whether the colors along the outer points by color agree. -/
theorem itcq_alF_spec {f fds fcm fco feq : ℕ} (hf : P.funs[f]? = some (itcqAlF fds fcm feq))
    (hds : ∀ (Z : PairCfg q) (z₀ : Fin q) {W : ℕ}, (rcCertIn Z z₀).wt ≤ W →
      FunDet P fds (rcCertIn Z z₀) (itcqDV Z) (itcqDsC W))
    (hcm : P.HasAt fcm (mapFuns fcm fco)) (hco : P.funs[fco]? = some itcqCoB)
    (heq : P.HasAt feq (eqNatsFuns feq)) (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q)
    (y₀ : Fin q) (w u : Val) {M : ℕ} (hM : (Val.list [itcqKs X x₀ Y y₀ w, u]).wt ≤ M) :
    FunDet P f (.list [itcqKs X x₀ Y y₀ w, u])
      (boolVal (decide (((itciFo X).map fun a => X.col a a) = (itciFo Y).map fun a => Y.col a a)))
      (itcqAlC M) := by
  set kv := itcqKs X x₀ Y y₀ w
  have hk : kv.wt ≤ M := (st_wt_mem (by simp)).trans hM
  have hcX : (rcCertIn X x₀).wt ≤ M := (st_wt_mem (by simp)).trans hk
  have hcY : (rcCertIn Y y₀).wt ≤ M := (st_wt_mem (by simp)).trans hk
  have hq : q < M := lt_of_lt_of_le (itcq_q_le X)
    ((st_wt_mem (show rcColVal X ∈ [rcColVal X, .nat X.j, .nat (x₀ : ℕ)] by simp)).trans hcX)
  have hdX : (itciFo X).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  have hdY : (itciFo Y).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  have hq2 : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hDX := itcq_dv_wt' X
  have hDY := itcq_dv_wt' Y
  have hwX := itcq_cols_wt X x₀
  have hwY := itcq_cols_wt Y y₀
  have hmX : (itciFo X).length * (2 * (rcCertIn X x₀).wt + 1) ≤ M * (2 * M + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmY : (itciFo Y).length * (2 * (rcCertIn Y y₀).wt + 1) ≤ M * (2 * M + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hMM : M * (2 * M + 1) ≤ 2 * (M + 1) ^ 2 := by nlinarith
  have x1 := wt_list2_le (rcCertIn X x₀) (itcqDV X)
  have x2 := wt_list2_le (rcCertIn Y y₀) (itcqDV Y)
  have x3 := wt_list2_le (natList ((itciFo X).map fun a => X.col a a))
    (natList ((itciFo Y).map fun a => Y.col a a))
  have hcolX := itcq_cols_spec hcm hco X x₀ (W := 20 * (M + 1) ^ 2)
    (show (Val.list [rcCertIn X x₀, itcqDV X]).wt ≤ 20 * (M + 1) ^ 2 by omega)
  have hcolY := itcq_cols_spec hcm hco Y y₀ (W := 20 * (M + 1) ^ 2)
    (show (Val.list [rcCertIn Y y₀, itcqDV Y]).wt ≤ 20 * (M + 1) ^ 2 by omega)
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 30 * (M + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hs2 := (Val.list [kv, u]).two_le_size
  have hs3 := (Val.list [kv, u]).size_le_wt
  have v0 := StDC.var' (P := P) (env := [.list [kv, u]]) (i := 0) rfl (W := Wl) (by omega)
  have k0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := kv) rfl (by omega)
  have kX := StDC.get k0 (StDC.nat 1 (by omega)) (v := rcCertIn X x₀) rfl (by omega)
  have kY := StDC.get k0 (StDC.nat 2 (by omega)) (v := rcCertIn Y y₀) rfl (by omega)
  have dX := StDC.call kX (hds X x₀ (W := M) hcX) (by omega)
  have dY := StDC.call kY (hds Y y₀ (W := M) hcY) (by omega)
  have cX := StDC.call (StDC.mk2 kX dX (by omega) (by omega)) hcolX (by omega)
  have cY := StDC.call (StDC.mk2 kY dY (by omega) (by omega)) hcolY (by omega)
  have hE := eqNats_spec heq ((itciFo X).map fun a => X.col a a)
    ((itciFo Y).map fun a => Y.col a a)
  have ce := StDC.call (StDC.mk2 cX cY (by omega) (by omega)) hE
    ((wt_boolVal_le _).trans (by omega))
  refine StDC.funDet hf ce ?_
  clear ce cY cX dY dX kY kX k0 v0
  unfold itcqAlC
  simp only [List.length_map] at *
  exact itcq_alC_arith hq hdX (n := 100) le_rfl hWl
    (B := (Val.list [natList ((itciFo X).map fun a => X.col a a),
      natList ((itciFo Y).map fun a => Y.col a a)]).wt) (by omega) (by omega)

end Prog

end GI.Impl
