import Workspace.Impl.AggItemCfDes
import Workspace.Impl.AggItemHvA

/-!
# Cases 2b and 3: the case dispatcher of the object step, and the wrap of the item output

* `itCfObF o2 o3` runs the Case 2b object step `o2` when the case code of `K.v` is `2`
  (`AggCase.code .twoB`) and the Case 3 step `o3` otherwise (`it_cfOb_spec`).
* `itCfWrF` puts the object part `wO'` of the kept value back around the kept value of the item
  stage: an ask `[1, mode, arg, kst]` becomes `[1, mode, arg, [wO', kst]]`
  (`it_cfWrA_spec`), and a finished branch `[0, [pcs, os, w']]` becomes
  `[0, [pcs, os, [wO', w']]]` (`it_cfWrD_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

/-- The dispatcher of the object step on the case code `K.v[2]`. -/
def itCfObF (o2 o3 : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 0) (.nat 2)) (.nat 2)) (.call o2 (.var 0)) (.call o3 (.var 0))

/-- **The dispatcher.** -/
theorem it_cfOb_spec {P : Program} {f o2 o3 : ℕ} (hf : P.funs[f]? = some (itCfObF o2 o3))
    (st dd srcV tb wO : Val) (cd : ℕ) {Q : Val → ℕ → Prop}
    (h2 : cd = 2 → FunAll P o2 (.list [.list [st, dd, .nat cd, srcV], tb, wO]) Q)
    (h3 : cd ≠ 2 → FunAll P o3 (.list [.list [st, dd, .nat cd, srcV], tb, wO]) Q) :
    FunAll P f (.list [.list [st, dd, .nat cd, srcV], tb, wO]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + 2 * w.wt + 100 * ((Val.list [.list [st, dd, .nat cd, srcV], tb, wO]).wt + 11)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [.list [st, dd, .nat cd, srcV], tb, wO]).wt := ⟨_, rfl⟩
  rw [← hX]
  have wK : (Val.list [st, dd, .nat cd, srcV]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wc : (Val.nat cd).wt < (Val.list [st, dd, .nat cd, srcV]).wt := wt_le_wt_list (by simp)
  have g := StDC.arith' (op := .eq) (StDC.get (StDC.arg (P := P) (W := X + 10)
      (vs := [.list [st, dd, .nat cd, srcV], tb, wO]) (rest := []) (j := 0)
      (v := .list [st, dd, .nat cd, srcV]) rfl (by omega) (by omega) (by omega))
      (StDC.nat 2 (by omega)) (v := .nat cd) (vs := [st, dd, .nat cd, srcV]) rfl (by omega))
    (StDC.nat 2 (by omega)) (z := if cd = 2 then 1 else 0) (by simp [GI.Machine.BinOp.eval])
    (by split_ifs <;> omega)
  have gv := StDC.var' (P := P) (W := X + 10)
    (env := [.list [.list [st, dd, .nat cd, srcV], tb, wO]]) (i := 0)
    (v := .list [.list [st, dd, .nat cd, srcV], tb, wO]) rfl (by omega)
  have gc := (g.mono (n' := 10) (E' := 0) (by omega) (by omega)).det
  have gv' := (gv.mono (n' := 1) (E' := 0) (by omega) (by omega)).det
  refine FunAll.intro hf (EvalAll.ite gc (fun vc cc h => ⟨_, h.1⟩) fun z cc ⟨hz, hcc⟩ => ?_)
  simp only [Val.nat.injEq] at hz
  subst hz
  by_cases h : cd = 2
  · rw [if_pos h]; simp only [one_ne_zero, if_false]
    refine EvalAll.call_funAll gv' fun v ca ⟨hv, hca⟩ => ?_
    subst hv
    exact ((h2 h).mono fun w cb hq => ⟨cb, hq, by omega⟩)
  · rw [if_neg h]; simp only [if_true]
    refine EvalAll.call_funAll gv' fun v ca ⟨hv, hca⟩ => ?_
    subst hv
    exact ((h3 h).mono fun w cb hq => ⟨cb, hq, by omega⟩)

/-- The wrap of the item output `r` (argument 1) with the object part `wO'` (argument 0). -/
def itCfWrF : Expr :=
  .ite (.get (arg 1) (.nat 0))
    (mk4 (.nat 1) (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 2))
      (mk2 (arg 0) (.get (arg 1) (.nat 3))))
    (mk2 (.nat 0) (mk3 (.get (.get (arg 1) (.nat 1)) (.nat 0))
      (.get (.get (arg 1) (.nat 1)) (.nat 1))
      (mk2 (arg 0) (.get (.get (arg 1) (.nat 1)) (.nat 2)))))

/-- The cost bound of the wrap. -/
def itCfWrC (X : ℕ) : ℕ := 10 ^ 4 * (X + 1) ^ 2

/-- **The wrap of an ask.** -/
theorem it_cfWrA_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itCfWrF)
    (wO md a kst : Val) :
    FunDet P f (.list [wO, .list [.nat 1, md, a, kst]])
      (.list [.nat 1, md, a, .list [wO, kst]])
      (itCfWrC (Val.list [wO, .list [.nat 1, md, a, kst]]).wt) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [wO, .list [.nat 1, md, a, kst]]).wt := ⟨_, rfl⟩
  rw [← hX]
  have wr : (Val.list [.nat 1, md, a, kst]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wo : wO.wt < X := hX ▸ wt_le_wt_list (by simp)
  have w1 : (Val.nat 1).wt < (Val.list [.nat 1, md, a, kst]).wt := wt_le_wt_list (by simp)
  have wm : md.wt < (Val.list [.nat 1, md, a, kst]).wt := wt_le_wt_list (by simp)
  have wa : a.wt < (Val.list [.nat 1, md, a, kst]).wt := wt_le_wt_list (by simp)
  have wk : kst.wt < (Val.list [.nat 1, md, a, kst]).wt := wt_le_wt_list (by simp)
  have h2 := wt_list2_le wO kst
  have h4 := wt_list4_le (.nat 1) md a (.list [wO, kst])
  have hn1 : (Val.nat 1).wt = 3 := by simp [wt_nat]
  set W := 20 * X + 40 with hW
  have gr : StDC P [.list [wO, .list [.nat 1, md, a, kst]]] (arg 1)
      (.list [.nat 1, md, a, kst]) 3 0 W :=
    StDC.arg (P := P) (vs := [wO, .list [.nat 1, md, a, kst]]) (j := 1) rfl (by omega) (by omega)
      (by omega)
  have g0 := StDC.get gr (StDC.nat 0 (by omega)) (v := .nat 1) rfl (by omega)
  have g1 := StDC.get gr (StDC.nat 1 (by omega)) (v := md) rfl (by omega)
  have g2 := StDC.get gr (StDC.nat 2 (by omega)) (v := a) rfl (by omega)
  have g3 := StDC.get gr (StDC.nat 3 (by omega)) (v := kst) rfl (by omega)
  have ga := StDC.arg (P := P) (W := W) (vs := [wO, .list [.nat 1, md, a, kst]]) (rest := [])
    (j := 0) (v := wO) rfl (by omega) (by omega) (by omega)
  have gt := StDC.mk4 (StDC.nat 1 (by omega)) g1 g2 (StDC.mk2 ga g3 (by omega) (by omega))
    (by omega) (by omega)
  refine StDC.funDet hf (itHv_ite1 (e := mk2 (.nat 0) (mk3 (.get (.get (arg 1) (.nat 1)) (.nat 0))
      (.get (.get (arg 1) (.nat 1)) (.nat 1))
      (mk2 (arg 0) (.get (.get (arg 1) (.nat 1)) (.nat 2))))) g0 one_ne_zero gt (by omega)) ?_
  unfold itCfWrC
  have : (X + 1) ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (X + 1) ^ 2 = (X + 1) * (X + 1) := by ring
  nlinarith

/-- **The wrap of a finished branch.** -/
theorem it_cfWrD_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itCfWrF)
    (wO pcs os w' : Val) :
    FunDet P f (.list [wO, .list [.nat 0, .list [pcs, os, w']]])
      (.list [.nat 0, .list [pcs, os, .list [wO, w']]])
      (itCfWrC (Val.list [wO, .list [.nat 0, .list [pcs, os, w']]]).wt) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [wO, .list [.nat 0, .list [pcs, os, w']]]).wt := ⟨_, rfl⟩
  rw [← hX]
  have wr : (Val.list [.nat 0, .list [pcs, os, w']]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wo : wO.wt < X := hX ▸ wt_le_wt_list (by simp)
  have w0 : (Val.nat 0).wt < (Val.list [.nat 0, .list [pcs, os, w']]).wt :=
    wt_le_wt_list (by simp)
  have wi : (Val.list [pcs, os, w']).wt < (Val.list [.nat 0, .list [pcs, os, w']]).wt :=
    wt_le_wt_list (by simp)
  have wp : pcs.wt < (Val.list [pcs, os, w']).wt := wt_le_wt_list (by simp)
  have wq : os.wt < (Val.list [pcs, os, w']).wt := wt_le_wt_list (by simp)
  have ww : w'.wt < (Val.list [pcs, os, w']).wt := wt_le_wt_list (by simp)
  have h2 := wt_list2_le wO w'
  have h3 := wt_list3_le pcs os (.list [wO, w'])
  have h2' := wt_list2_le (.nat 0) (.list [pcs, os, .list [wO, w']])
  have hn0 : (Val.nat 0).wt = 2 := by simp [wt_nat]
  set W := 40 * X + 80 with hW
  have gr : StDC P [.list [wO, .list [.nat 0, .list [pcs, os, w']]]] (arg 1)
      (.list [.nat 0, .list [pcs, os, w']]) 3 0 W :=
    StDC.arg (P := P) (vs := [wO, .list [.nat 0, .list [pcs, os, w']]]) (j := 1) rfl (by omega)
      (by omega) (by omega)
  have g0 := StDC.get gr (StDC.nat 0 (by omega)) (v := .nat 0) rfl (by omega)
  have gi := StDC.get gr (StDC.nat 1 (by omega)) (v := .list [pcs, os, w']) rfl (by omega)
  have gp := StDC.get gi (StDC.nat 0 (by omega)) (v := pcs) rfl (by omega)
  have gq := StDC.get gi (StDC.nat 1 (by omega)) (v := os) rfl (by omega)
  have gw := StDC.get gi (StDC.nat 2 (by omega)) (v := w') rfl (by omega)
  have ga := StDC.arg (P := P) (W := W) (vs := [wO, .list [.nat 0, .list [pcs, os, w']]])
    (rest := []) (j := 0) (v := wO) rfl (by omega) (by omega) (by omega)
  have ge := StDC.mk2 (StDC.nat 0 (by omega)) (StDC.mk3 gp gq (StDC.mk2 ga gw (by omega) (by omega))
    (by omega) (by omega)) (by omega) (by omega)
  refine StDC.funDet hf (itHv_ite0 (t := mk4 (.nat 1) (.get (arg 1) (.nat 1))
      (.get (arg 1) (.nat 2)) (mk2 (arg 0) (.get (arg 1) (.nat 3)))) g0 ge (by omega)) ?_
  unfold itCfWrC
  have : (X + 1) ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (X + 1) ^ 2 = (X + 1) * (X + 1) := by ring
  nlinarith

end GI.Impl
