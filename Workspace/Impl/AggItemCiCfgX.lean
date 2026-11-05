module

public import Workspace.Impl.AggItemCiCfgW

@[expose] public section

/-!
# The configuration query: the start program of the configuration branch

`itcqStF fl fa` on the item input `[K.v, stTv b, ⟨oX⟩, ⟨oY⟩, w]` with `oX = pair X x₀`,
`oY = pair Y y₀` (Algorithm `alg:auxiliary`, the branch `q ≤ λ`):
* computes the fiber lists `C_X`, `C_Y` (`itcqFlF`);
* if `|C_X| ≠ |C_Y|`, returns the empty result `[0, [⟨⟩, ⟨⟩, w]]` ("**if** `|C_X| ≠ |C_Y|`
  **then return** the empty list");
* otherwise asks the configuration query: `[1, solve, arg, kst]` with `arg = itcqArg X Y hc`
  the canonical value of the pair structure (`itcqArgF`) and the kept state
  `kst = [w, cert X, cert Y, C_X, C_Y]` (`itcqKs`).

`itcq_stF_spec` gives the value `itcqStV` at cost `itcqStC W`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- The kept state of the configuration query. -/
def itcqKs (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val) : Val :=
  .list [w, rcCertIn X x₀, rcCertIn Y y₀, itcqFV X, itcqFV Y]

/-- The empty result with the kept value `w`. -/
def itcqEmp (w : Val) : Val := .list [.nat 0, .list [.list [], .list [], w]]

open Classical in
/-- What the start program returns. -/
noncomputable def itcqStV (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) (w : Val) :
    Val :=
  if hc : X.fiber.card = Y.fiber.card then
    .list [.nat 1, .nat 0, itcqArg X Y hc, itcqKs X x₀ Y y₀ w]
  else itcqEmp w

/-- **The start program** of the configuration branch. -/
def itcqStF (fl fa : ℕ) : Expr :=
  .letE (.get (arg 2) (.nat 1))
  (.letE (.get (arg 3) (.nat 1))
  (.letE (arg 4)
  (.letE (.call fl (.var 1))
  (.letE (.call fl (.var 2))
  (.letE (.length (.var 4))
  (.ite (.arith .eq (.length (.var 5)) (.var 6))
    (mk4 (.nat 1) (.nat 0)
      (.call fa (mk2 (mk3 (.get (.var 1) (.nat 0)) (.var 4) (.var 6))
        (mk3 (.get (.var 2) (.nat 0)) (.var 5) (.var 6))))
      (itcqMkL [.var 3, .var 1, .var 2, .var 4, .var 5]))
    (mk2 (.nat 0) (mk3 .nil .nil (.var 3)))))))))

/-- The weight bound of the inputs of `itcqArgF` inside the start program. -/
def itcqSA (W : ℕ) : ℕ := 100 * (W + 2) ^ 2

/-- The weight bound inside the start program. -/
def itcqSV (W : ℕ) : ℕ := 3 * itcqAV (itcqSA W)

/-- The cost bound of the start program. -/
def itcqStC (W : ℕ) : ℕ := 2 * itcqFlC W + itcqArgC (itcqSA W) + 300 * (itcqSV W + 1)

theorem itcq_fv_len (Z : PairCfg q) :
    (((itciFl Z.fiber).map Fin.val).map Val.nat).length = Z.fiber.card := by
  simp [itciFl_length]

section Prog

variable {P : Program}

set_option maxHeartbeats 1000000 in
/-- **The start program** gives `itcqStV` in cost `itcqStC W`, `W` at least the input weight. -/
theorem itcq_stF_spec {f fl fr ff fb fa : ℕ} (hf : P.funs[f]? = some (itcqStF fl fa))
    (hfl : P.funs[fl]? = some (itcqFlF fr ff)) (hr : P.HasAt fr (rangeFuns fr))
    (hff : P.HasAt ff (filterFuns ff fb)) (hfb : P.funs[fb]? = some itcqFbT)
    (harg : ∀ (X Y : PairCfg q) (hc : X.fiber.card = Y.fiber.card) {W : ℕ},
      (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]).wt ≤ W →
      FunDet P fa (.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]) (itcqArg X Y hc)
        (itcqArgC W))
    (Kv tb w : Val) (X : PairCfg q) (x₀ : Fin q) (Y : PairCfg q) (y₀ : Fin q) {W : ℕ}
    (hW : (Val.list [Kv, tb, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w]).wt ≤ W) :
    FunDet P f (.list [Kv, tb, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w])
      (itcqStV X x₀ Y y₀ w) (itcqStC W) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S, S = (W + 2) ^ 2 := ⟨_, rfl⟩
  have hS1 : W + 2 ≤ S := by rw [hS]; nlinarith
  set vs : List Val := [Kv, tb, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w] with hvs
  set cX := rcCertIn X x₀ with hcX
  set cY := rcCertIn Y y₀ with hcY
  have hoX : (itCfOutV (.pair X x₀)).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hoY : (itCfOutV (.pair Y y₀)).wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hww : w.wt < W := lt_of_lt_of_le (wt_le_wt_list (by simp [hvs])) hW
  have hcXw : cX.wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (vs := [.nat 2, cX]) (by simp)) hoX.le
  have hcYw : cY.wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (vs := [.nat 2, cY]) (by simp)) hoY.le
  have hcolX : (rcColVal X).wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (vs := [rcColVal X, .nat X.j, .nat x₀]) (by simp)) hcXw.le
  have hcolY : (rcColVal Y).wt < W :=
    lt_of_lt_of_le (wt_le_wt_list (vs := [rcColVal Y, .nat Y.j, .nat y₀]) (by simp)) hcYw.le
  have hq := itcq_q_le X
  have hsq : (q + 1) ^ 2 ≤ S := by rw [hS]; exact Nat.pow_le_pow_left (by omega) 2
  have hFX : (itcqFV X).wt ≤ 5 * S := by have := itcq_fv_wt X; omega
  have hFY : (itcqFV Y).wt ≤ 5 * S := by have := itcq_fv_wt Y; omega
  have hnX : X.fiber.card ≤ q := by simpa using Finset.card_le_univ X.fiber
  have hnY : Y.fiber.card ≤ q := by simpa using Finset.card_le_univ Y.fiber
  have hnXw := wt_nat_le X.fiber.card
  have hnYw := wt_nat_le Y.fiber.card
  -- the bounds
  set Wa := itcqSA W with hWa
  set Wd := itcqSV W with hWd
  have hSa : 100 * S = Wa := by rw [hWa, itcqSA, hS]
  have hAV : Wa + 2 ≤ itcqAV Wa := by
    unfold itcqAV
    have : Wa + 2 ≤ (Wa + 2) ^ 8 := Nat.le_self_pow (by norm_num) _
    omega
  have hWd3 : Wd = 3 * itcqAV Wa := rfl
  -- the inputs of `itcqArgF`
  have hzX := wt_list3_le (rcColVal X) (itcqFV X) (.nat X.fiber.card)
  have hzY := wt_list3_le (rcColVal Y) (itcqFV Y) (.nat X.fiber.card)
  have hz2 := wt_list2_le (itcqZ X X.fiber.card) (itcqZ Y X.fiber.card)
  have hzXw : (itcqZ X X.fiber.card).wt ≤ 20 * S := by unfold itcqZ; omega
  have hzYw : (itcqZ Y X.fiber.card).wt ≤ 20 * S := by unfold itcqZ; omega
  have hz2w : (Val.list [itcqZ X X.fiber.card, itcqZ Y X.fiber.card]).wt ≤ Wa := by omega
  have hks := wt_list_le [w, cX, cY, itcqFV X, itcqFV Y]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at hks
  have hksw : (itcqKs X x₀ Y y₀ w).wt ≤ 30 * S := by
    show (Val.list [w, cX, cY, itcqFV X, itcqFV Y]).wt ≤ 30 * S; omega
  have hemp : (itcqEmp w).wt ≤ 2 * (2 + (2 * (4 + 4 + w.wt) + 7)) + 6 := by
    have h1 := wt_list2_le (.nat 0) (.list [.list [], .list [], w])
    have h2 := wt_list3_le (.list []) (.list []) w
    have := wt_nat_le 0
    simp only [wt_list_nil] at h2
    unfold itcqEmp; omega
  -- the environment after the six `let`s
  set env : List Val := [.list vs, cX, cY, w, itcqFV X, itcqFV Y, .nat X.fiber.card] with henv
  have v1 := StDC.var' (P := P) (env := env) (i := 1) (W := Wd) rfl (by omega)
  have v2 := StDC.var' (P := P) (env := env) (i := 2) (W := Wd) rfl (by omega)
  have v3 := StDC.var' (P := P) (env := env) (i := 3) (W := Wd) rfl (by omega)
  have v4 := StDC.var' (P := P) (env := env) (i := 4) (W := Wd) rfl (by omega)
  have v5 := StDC.var' (P := P) (env := env) (i := 5) (W := Wd) rfl (by omega)
  have v6 := StDC.var' (P := P) (env := env) (i := 6) (W := Wd) rfl (by omega)
  have ln5 := StDC.length v5 (vs := ((itciFl Y.fiber).map Fin.val).map Val.nat)
    (by rw [itcq_fv_len]; omega)
  rw [itcq_fv_len] at ln5
  have tst := StDC.arith (op := .eq) ln5 v6 rfl ((wt_nat_le _).trans (by
    simp only [Machine.BinOp.eval_eq]; split_ifs <;> omega))
  have inner : StDC P env (.ite (.arith .eq (.length (.var 5)) (.var 6))
      (mk4 (.nat 1) (.nat 0)
        (.call fa (mk2 (mk3 (.get (.var 1) (.nat 0)) (.var 4) (.var 6))
          (mk3 (.get (.var 2) (.nat 0)) (.var 5) (.var 6))))
        (itcqMkL [.var 3, .var 1, .var 2, .var 4, .var 5]))
      (mk2 (.nat 0) (mk3 .nil .nil (.var 3)))) (itcqStV X x₀ Y y₀ w) 200
        (itcqArgC Wa) Wd := by
    by_cases hc : X.fiber.card = Y.fiber.card
    · have hv : itcqStV X x₀ Y y₀ w =
          .list [.nat 1, .nat 0, itcqArg X Y hc, itcqKs X x₀ Y y₀ w] := by
        rw [itcqStV, dif_pos hc]
      have hAw := itcq_arg_wt X Y hc hz2w
      have hout := wt_list4_le (.nat 1) (.nat 0) (itcqArg X Y hc) (itcqKs X x₀ Y y₀ w)
      have h01 := wt_nat_le 1
      have h00 := wt_nat_le 0
      have houtw : (itcqStV X x₀ Y y₀ w).wt ≤ Wd := by rw [hv]; omega
      rw [hv] at houtw ⊢
      refine (StDC.ite (ne := 0) (Ee := 0) (nt := 150) (Et := itcqArgC Wa) tst (fun _ => ?_) (fun h0 => absurd h0 (by
        simp only [Machine.BinOp.eval_eq, if_pos hc.symm]; omega)) houtw).mono
        (by omega) (by omega)
      have gX := StDC.get v1 (StDC.nat 0 (by omega)) (v := rcColVal X) rfl (by omega)
      have gY := StDC.get v2 (StDC.nat 0 (by omega)) (v := rcColVal Y) rfl (by omega)
      have mX := StDC.mk3 gX v4 v6 (show (itcqZ X X.fiber.card).wt ≤ Wd by omega) (by omega)
      have v5' : StDC P env (.var 5) (itcqFV Y) 1 0 Wd := v5
      have mY := StDC.mk3 gY v5' v6 (show (itcqZ Y X.fiber.card).wt ≤ Wd by omega) (by omega)
      have m2 := StDC.mk2 mX mY (show (Val.list [itcqZ X X.fiber.card,
        itcqZ Y X.fiber.card]).wt ≤ Wd by omega) (by omega)
      have ca := StDC.call m2 (harg X Y hc hz2w) (by omega)
      have ks := itcq_mkL_spec (P := P) (env := env) (W := Wd)
        (es := [.var 3, .var 1, .var 2, .var 4, .var 5])
        (vs := [w, cX, cY, itcqFV X, itcqFV Y])
        (.cons v3 (.cons v1 (.cons v2 (.cons v4 (.cons v5 .nil)))))
        (show (itcqKs X x₀ Y y₀ w).wt ≤ Wd by omega) (by omega)
      have := StDC.mk4 (StDC.nat 1 (P := P) (env := env) (W := Wd) (by omega))
        (StDC.nat 0 (by omega)) ca ks
        (show (Val.list [.nat 1, .nat 0, itcqArg X Y hc, itcqKs X x₀ Y y₀ w]).wt ≤ Wd by omega)
        (by omega)
      exact this.mono (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
    · have hv : itcqStV X x₀ Y y₀ w = itcqEmp w := by rw [itcqStV, dif_neg hc]
      have houtw : (itcqEmp w).wt ≤ Wd := by omega
      rw [hv]
      refine (StDC.ite (nt := 0) (Et := 0) (ne := 20) (Ee := 0) tst (fun h1 => absurd h1 (by
        simp only [Machine.BinOp.eval_eq, if_neg (Ne.symm hc)]; omega)) (fun _ => ?_)
        houtw).mono (by omega) (by omega)
      have h3 := StDC.mk3 (StDC.nil (P := P) (env := env) (W := Wd) (by omega))
        (StDC.nil (by omega)) v3 (show (Val.list [.list [], .list [], w]).wt ≤ Wd by
          have := wt_list3_le (.list []) (.list []) w; simp only [wt_list_nil] at this; omega)
        (by omega)
      exact (StDC.mk2 (StDC.nat 0 (by omega)) h3 houtw (by omega)).mono (by omega) le_rfl
  have hinw : (itcqStV X x₀ Y y₀ w).wt ≤ Wd := by
    by_cases hc : X.fiber.card = Y.fiber.card
    · rw [itcqStV, dif_pos hc]
      have hAw := itcq_arg_wt X Y hc hz2w
      have hout := wt_list4_le (.nat 1) (.nat 0) (itcqArg X Y hc) (itcqKs X x₀ Y y₀ w)
      have h01 := wt_nat_le 1
      have h00 := wt_nat_le 0
      omega
    · rw [itcqStV, dif_neg hc]; omega
  -- the six `let`s, from the inside out
  have ln4 := StDC.length (P := P) (env := [.list vs, cX, cY, w, itcqFV X, itcqFV Y])
    (StDC.var' (i := 4) (v := itcqFV X) (W := Wd) rfl (by omega))
    (vs := ((itciFl X.fiber).map Fin.val).map Val.nat) (by rw [itcq_fv_len]; omega)
  rw [itcq_fv_len] at ln4
  have L6 := StDC.letE ln4 inner hinw
  have hflX : FunDet P fl cX (itcqFV X) (itcqFlC W) :=
    itcq_flF_spec (z₀ := x₀) hfl hr hff hfb X (by show cX.wt ≤ W; omega)
  have hflY : FunDet P fl cY (itcqFV Y) (itcqFlC W) :=
    itcq_flF_spec (z₀ := y₀) hfl hr hff hfb Y (by show cY.wt ≤ W; omega)
  have L5 := StDC.letE (StDC.call (StDC.var' (P := P) (env := [.list vs, cX, cY, w, itcqFV X])
    (i := 2) (W := Wd) rfl (by omega)) hflY (by omega)) L6 hinw
  have L4 := StDC.letE (StDC.call (StDC.var' (P := P) (env := [.list vs, cX, cY, w])
    (i := 1) (W := Wd) rfl (by omega)) hflX (by omega)) L5 hinw
  have L3 := StDC.letE (StDC.arg (P := P) (rest := [cX, cY]) (vs := vs) (j := 4) (W := Wd) rfl
    (by omega) (by omega) (by omega)) L4 hinw
  have L2 := StDC.letE (StDC.get (StDC.arg (P := P) (rest := [cX]) (vs := vs) (j := 3) (W := Wd)
    (v := itCfOutV (.pair Y y₀)) rfl (by omega) (by omega) (by omega)) (StDC.nat 1 (by omega))
    (v := cY) rfl (by omega)) L3 hinw
  have L1 := StDC.letE (StDC.get (StDC.arg (P := P) (rest := []) (vs := vs) (j := 2) (W := Wd)
    (v := itCfOutV (.pair X x₀)) rfl (by omega) (by omega) (by omega)) (StDC.nat 1 (by omega))
    (v := cX) rfl (by omega)) L2 hinw
  refine StDC.funDet hf L1 ?_
  show _ ≤ 2 * itcqFlC W + itcqArgC Wa + 300 * (Wd + 1)
  omega

end Prog

end GI.Impl
