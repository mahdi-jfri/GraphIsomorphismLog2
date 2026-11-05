module

public import Workspace.Impl.AggItemCfWr

@[expose] public section

/-!
# Cases 2b and 3: the init, start, continue and branch-step programs

The kept value of Cases 2b/3 is `[wO, wI]`: the object part `wO = [⟨H_X⟩, ⟨H_Y⟩, ⟨c_X⟩, ⟨cache⟩]`
(`itCfWO`) and the kept value `wI` of the item stage.

* `itCfIF` (init, on `K.v`): the two groups of second parts, the orbital coloring `c_X` of the
  source, the item init; returns `[[⟨H_X⟩, ⟨H_Y⟩, ⟨c_X⟩, []], wI]` (`it_cfI_spec`).
* `itCfStF` (start, on `[K.v, ⟨b⟩, [wO, wI]]`): the objects of the branch (`itCfObF`), the item
  start on `[K.v, ⟨b⟩, ⟨oX⟩, ⟨oY⟩, wI]`, the wrap (`it_cfSt_spec`).
* `itCfCtF` (continue, on `[[wO', kst], u]`): the item step on `[kst, u]` and the wrap
  (`it_cfCt_spec`).
* `itCfBF` (branch step): start on a list of three entries, continue otherwise (`it_cfB_spec`).

The specifications here are generic: the callees enter through their own specifications.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

/-! ### The wrap, for both shapes -/

/-- The two shapes of an item output: an ask `[1, mode, arg, kst]` or a finished branch
`[0, [pcs, os, w']]`. -/
def ItCfShape (r : Val) : Prop :=
  (∃ md a kst : Val, r = .list [.nat 1, md, a, kst]) ∨
    (∃ pcs os w' : Val, r = .list [.nat 0, .list [pcs, os, w']])

/-- The wrap of `r` with `wO`. -/
def ItCfWrRel (wO r w : Val) : Prop :=
  (∃ md a kst : Val, r = .list [.nat 1, md, a, kst] ∧ w = .list [.nat 1, md, a, .list [wO, kst]]) ∨
    (∃ pcs os w' : Val, r = .list [.nat 0, .list [pcs, os, w']] ∧
      w = .list [.nat 0, .list [pcs, os, .list [wO, w']]])

theorem it_cfWr_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itCfWrF) (wO r : Val)
    (hr : ItCfShape r) :
    FunAll P f (.list [wO, r]) (fun w c => ItCfWrRel wO r w ∧ c ≤ itCfWrC (Val.list [wO, r]).wt) := by
  rcases hr with ⟨md, a, kst, rfl⟩ | ⟨pcs, os, w', rfl⟩
  · exact FunAll.mono (it_cfWrA_spec hf wO md a kst) fun w c ⟨hw, hc⟩ =>
      ⟨Or.inl ⟨md, a, kst, rfl, hw⟩, hc⟩
  · exact FunAll.mono (it_cfWrD_spec hf wO pcs os w') fun w c ⟨hw, hc⟩ =>
      ⟨Or.inr ⟨pcs, os, w', rfl, hw⟩, hc⟩

theorem itCfWrC_mono {a b : ℕ} (h : a ≤ b) : itCfWrC a ≤ itCfWrC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-! ### The start of a branch -/

/-- The start of the branch on `[K.v, ⟨b⟩, [wO, wI]]`. -/
def itCfStF (ob fs wr : ℕ) : Expr :=
  .letE (.call ob (mk3 (arg 0) (arg 1) (.get (arg 2) (.nat 0))))
  (.letE (.call fs (.snoc (mk4 (arg 0) (arg 1) (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1)))
      (.get (arg 2) (.nat 1))))
    (.call wr (mk2 (.get (.var 1) (.nat 2)) (.var 2))))

/-- The cost bound of the start, for the input weight `X` and the callee bounds `Bo`, `Bs`. -/
def itCfStC (X Bo Bs : ℕ) : ℕ := 1000 * (X + Bo + Bs + 10) + 5 * itCfWrC (4 * (Bo + Bs) + 6)

set_option maxHeartbeats 2000000 in
theorem it_cfSt_spec {P : Program} {f ob fs wr : ℕ} (hf : P.funs[f]? = some (itCfStF ob fs wr))
    (hwr : P.funs[wr]? = some itCfWrF) (Kv tb wO wI : Val) {Bo Bs : ℕ}
    {Qo : Val → Val → Val → Prop} {Qs : Val → Val → Val → Val → Prop}
    (hob : FunAll P ob (.list [Kv, tb, wO]) (fun w c =>
      ∃ oX oY wO', w = .list [oX, oY, wO'] ∧ Qo oX oY wO' ∧ c ≤ Bo))
    (hfs : ∀ oX oY wO', Qo oX oY wO' →
      FunAll P fs (.list [Kv, tb, oX, oY, wI]) (fun r c => Qs oX oY wO' r ∧ ItCfShape r ∧ c ≤ Bs)) :
    FunAll P f (.list [Kv, tb, .list [wO, wI]]) (fun w c => ∃ oX oY wO' r, Qo oX oY wO' ∧
      Qs oX oY wO' r ∧ ItCfWrRel wO' r w ∧
      c ≤ itCfStC (Val.list [Kv, tb, .list [wO, wI]]).wt Bo Bs) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [Kv, tb, .list [wO, wI]]).wt := ⟨_, rfl⟩
  rw [← hX]
  have wK : Kv.wt < X := hX ▸ wt_le_wt_list (by simp)
  have wt : tb.wt < X := hX ▸ wt_le_wt_list (by simp)
  have ww : (Val.list [wO, wI]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wO_ : wO.wt < (Val.list [wO, wI]).wt := wt_le_wt_list (by simp)
  have wI_ : wI.wt < (Val.list [wO, wI]).wt := wt_le_wt_list (by simp)
  have h3 := wt_list3_le Kv tb wO
  have e3 : (Val.list [Kv, tb, .list [wO, wI]]).wt = X := hX.symm
  have a1 := Det.mk3 (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]]) (rest := []) (j := 0)
      (v := Kv) rfl)
    (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]]) (rest := []) (j := 1) (v := tb) rfl)
    (Det.get' (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]]) (rest := []) (j := 2)
      (v := .list [wO, wI]) rfl) (Det.nat 0) (v := wO) (vs := [wO, wI]) rfl)
  refine FunAll.intro hf (EvalAll.letE (Ra := fun v c => ∃ oX oY wO', v = .list [oX, oY, wO'] ∧
      Qo oX oY wO' ∧ v.wt < Bo ∧ c ≤ 100 * (X + 1) + 2 * Bo + 1)
    (EvalAll.call_funAll a1 fun v ca ⟨hv, hca⟩ => by
      subst hv
      exact hob.wt_lt.mono fun w c ⟨⟨oX, oY, wO', hw, hq, hc⟩, hwc⟩ =>
        ⟨oX, oY, wO', hw, hq, by omega, by rw [e3] at hca; omega⟩) fun v1 c1 hv1 => ?_)
  obtain ⟨oX, oY, wO', rfl, hq, hv1w, hc1⟩ := hv1
  have wx : oX.wt < (Val.list [oX, oY, wO']).wt := wt_le_wt_list (by simp)
  have wy : oY.wt < (Val.list [oX, oY, wO']).wt := wt_le_wt_list (by simp)
  have wo : wO'.wt < (Val.list [oX, oY, wO']).wt := wt_le_wt_list (by simp)
  set env1 : List Val := [.list [Kv, tb, .list [wO, wI]], .list [oX, oY, wO']] with henv1
  have g1 : Det P env1 (.var 1) (.list [oX, oY, wO']) ((Val.list [oX, oY, wO']).wt + 1) :=
    Det.var' rfl
  have h5 := wt_list_le [Kv, tb, oX, oY, wI]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h5
  have a2 := Det.snoc (Det.mk4 (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]])
      (rest := [.list [oX, oY, wO']]) (j := 0) (v := Kv) rfl)
    (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]]) (rest := [.list [oX, oY, wO']]) (j := 1)
      (v := tb) rfl)
    (Det.get' g1 (Det.nat 0) (v := oX) (vs := [oX, oY, wO']) rfl)
    (Det.get' g1 (Det.nat 1) (v := oY) (vs := [oX, oY, wO']) rfl))
    (Det.get' (Det.arg' (P := P) (vs := [Kv, tb, .list [wO, wI]])
      (rest := [.list [oX, oY, wO']]) (j := 2) (v := .list [wO, wI]) rfl) (Det.nat 1) (v := wI)
      (vs := [wO, wI]) rfl)
  have h4 := wt_list4_le Kv tb oX oY
  have e5 : (Val.list ([Kv, tb, oX, oY] ++ [wI])).wt = (Val.list [Kv, tb, oX, oY, wI]).wt := rfl
  refine EvalAll.letE (Ra := fun r c => Qs oX oY wO' r ∧ ItCfShape r ∧ r.wt < Bs ∧
      c ≤ 100 * (X + Bo + 10) + 2 * Bs + 1)
    (EvalAll.call_funAll a2 fun v ca ⟨hv, hca⟩ => by
      subst hv
      exact (hfs oX oY wO' hq).wt_lt.mono fun w c ⟨⟨hq2, hsh, hc⟩, hwc⟩ =>
        ⟨hq2, hsh, by omega, by rw [e5] at hca; rw [e3] at hca; omega⟩) fun r c2 hr => ?_
  obtain ⟨hq2, hsh, hrw, hc2⟩ := hr
  set env2 : List Val := env1 ++ [r] with henv2
  have a3 := Det.mk2 (Det.get' (Det.var' (P := P) (env := env2) (i := 1)
      (v := .list [oX, oY, wO']) rfl) (Det.nat 2) (v := wO') (vs := [oX, oY, wO']) rfl)
    (Det.var' (P := P) (env := env2) (i := 2) (v := r) rfl)
  have h2 := wt_list2_le wO' r
  refine EvalAll.call_funAll a3 fun v ca ⟨hv, hca⟩ => ?_
  subst hv
  refine (it_cfWr_spec hwr wO' r hsh).wt_lt.mono fun w c ⟨⟨hw, hc⟩, hwc⟩ =>
    ⟨oX, oY, wO', r, hq, hq2, hw, ?_⟩
  have hc' : c ≤ itCfWrC (Val.list [wO', r]).wt := hc
  have hm := itCfWrC_mono (show (Val.list [wO', r]).wt ≤ 4 * (Bo + Bs) + 6 by omega)
  unfold itCfStC
  omega

/-! ### The continuation of a branch -/

/-- The continuation on `[[wO', kst], u]`. -/
def itCfCtF (fk wr : ℕ) : Expr :=
  .letE (.call fk (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
    (.call wr (mk2 (.get (arg 0) (.nat 0)) (.var 1)))

/-- The cost bound of the continuation. -/
def itCfCtC (X Bk : ℕ) : ℕ := 1000 * (X + Bk + 10) + 5 * itCfWrC (4 * (X + Bk) + 6)

set_option maxHeartbeats 2000000 in
theorem it_cfCt_spec {P : Program} {f fk wr : ℕ} (hf : P.funs[f]? = some (itCfCtF fk wr))
    (hwr : P.funs[wr]? = some itCfWrF) (wO kst u : Val) {Bk : ℕ} {Qk : Val → Prop}
    (hfk : FunAll P fk (.list [kst, u]) (fun r c => Qk r ∧ ItCfShape r ∧ c ≤ Bk)) :
    FunAll P f (.list [.list [wO, kst], u]) (fun w c => ∃ r, Qk r ∧ ItCfWrRel wO r w ∧
      c ≤ itCfCtC (Val.list [.list [wO, kst], u]).wt Bk) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [.list [wO, kst], u]).wt := ⟨_, rfl⟩
  rw [← hX]
  have e : (Val.list [.list [wO, kst], u]).wt = X := hX.symm
  have w1 : (Val.list [wO, kst]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wu : u.wt < X := hX ▸ wt_le_wt_list (by simp)
  have wo : wO.wt < (Val.list [wO, kst]).wt := wt_le_wt_list (by simp)
  have wk : kst.wt < (Val.list [wO, kst]).wt := wt_le_wt_list (by simp)
  have h2 := wt_list2_le kst u
  have a1 := Det.mk2 (Det.get' (Det.arg' (P := P) (vs := [.list [wO, kst], u]) (rest := [])
      (j := 0) (v := .list [wO, kst]) rfl) (Det.nat 1) (v := kst) (vs := [wO, kst]) rfl)
    (Det.arg' (P := P) (vs := [.list [wO, kst], u]) (rest := []) (j := 1) (v := u) rfl)
  refine FunAll.intro hf (EvalAll.letE (Ra := fun r c => Qk r ∧ ItCfShape r ∧ r.wt < Bk ∧
      c ≤ 20 * (X + 1) + 2 * Bk + 1)
    (EvalAll.call_funAll a1 fun v ca ⟨hv, hca⟩ => by
      subst hv
      exact hfk.wt_lt.mono fun w c ⟨⟨hq, hsh, hc⟩, hwc⟩ => ⟨hq, hsh, by omega, by
        rw [e] at hca; omega⟩) fun r c1 hr => ?_)
  obtain ⟨hq, hsh, hrw, hc1⟩ := hr
  have a2 := Det.mk2 (Det.get' (Det.arg' (P := P) (vs := [.list [wO, kst], u]) (rest := [r])
      (j := 0) (v := .list [wO, kst]) rfl) (Det.nat 0) (v := wO) (vs := [wO, kst]) rfl)
    (Det.var' (P := P) (env := [.list [.list [wO, kst], u], r]) (i := 1) (v := r) rfl)
  have h2' := wt_list2_le wO r
  refine EvalAll.call_funAll a2 fun v ca ⟨hv, hca⟩ => ?_
  subst hv
  refine (it_cfWr_spec hwr wO r hsh).wt_lt.mono fun w c ⟨⟨hw, hc⟩, hwc⟩ => ⟨r, hq, hw, ?_⟩
  have hc' : c ≤ itCfWrC (Val.list [wO, r]).wt := hc
  have hm := itCfWrC_mono (show (Val.list [wO, r]).wt ≤ 4 * (X + Bk) + 6 by omega)
  unfold itCfCtC
  rw [e] at hca
  omega

/-! ### The branch step -/

/-- The branch step: start on three entries, continue otherwise. -/
def itCfBF (st ct : ℕ) : Expr :=
  .ite (.arith .eq (.length (.var 0)) (.nat 3)) (.call st (.var 0)) (.call ct (.var 0))

theorem it_cfB_spec {P : Program} {f st ct : ℕ} (hf : P.funs[f]? = some (itCfBF st ct))
    (vs : List Val) {Q : Val → ℕ → Prop}
    (h3 : vs.length = 3 → FunAll P st (.list vs) Q)
    (h2 : vs.length ≠ 3 → FunAll P ct (.list vs) Q) :
    FunAll P f (.list vs) (fun w c => ∃ c', Q w c' ∧ c ≤ c' + 2 * w.wt + 100 * ((Val.list vs).wt + 11)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list vs).wt := ⟨_, rfl⟩
  rw [← hX]
  have hl : vs.length < X := hX ▸ length_lt_wt_list vs
  have g := StDC.arith' (op := .eq) (StDC.length (StDC.var' (P := P) (W := X + 10)
      (env := [.list vs]) (i := 0) (v := .list vs) rfl (by omega)) (by omega))
    (StDC.nat 3 (by omega)) (z := if vs.length = 3 then 1 else 0)
    (by simp [GI.Machine.BinOp.eval]) (by split_ifs <;> omega)
  have gv := StDC.var' (P := P) (W := X + 10) (env := [.list vs]) (i := 0) (v := .list vs) rfl
    (by omega)
  have gc := (g.mono (n' := 10) (E' := 0) (by omega) (by omega)).det
  have gv' := (gv.mono (n' := 1) (E' := 0) (by omega) (by omega)).det
  refine FunAll.intro hf (EvalAll.ite gc (fun vc cc h => ⟨_, h.1⟩) fun z cc ⟨hz, hcc⟩ => ?_)
  simp only [Val.nat.injEq] at hz
  subst hz
  by_cases h : vs.length = 3
  · rw [if_pos h]; simp only [one_ne_zero, if_false]
    refine EvalAll.call_funAll gv' fun v ca ⟨hv, hca⟩ => ?_
    subst hv
    exact ((h3 h).mono fun w cb hq => ⟨cb, hq, by omega⟩)
  · rw [if_neg h]; simp only [if_true]
    refine EvalAll.call_funAll gv' fun v ca ⟨hv, hca⟩ => ?_
    subst hv
    exact ((h2 h).mono fun w cb hq => ⟨cb, hq, by omega⟩)

/-! ### The init -/

/-- The init on `K.v = [st, dd, code, src]`, with `st = [sv, [k, q], ps, fx, fy, cv]`. -/
def itCfIF (grp fcol fi : ℕ) : Expr :=
  .letE (.call grp (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 3))))
  (.letE (.call grp (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.get (arg 0) (.nat 4))))
  (.letE (.call fcol (mk3 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.var 1) (arg 3)))
  (.letE (.call fi (.var 0))
    (mk2 (mk4 (.var 1) (.var 2) (.var 3) .nil) (.var 4)))))

/-- The cost bound of the init. -/
def itCfIC (X Bg Bc Bi : ℕ) : ℕ := 1000 * (X + Bg + Bc + Bi + 10)

set_option maxHeartbeats 2000000 in
theorem it_cfI_spec {P : Program} {f grp fcol fi : ℕ} (hf : P.funs[f]? = some (itCfIF grp fcol fi))
    (sv psV fxV fyV cv dd cd srcV gx gy cX : Val) (k q : ℕ) {Bg Bc Bi : ℕ} {Qi : Val → Prop}
    (hgx : FunDet P grp (.list [.nat q, fxV]) gx Bg) (hgy : FunDet P grp (.list [.nat q, fyV]) gy Bg)
    (hcol : FunDet P fcol (.list [.nat q, gx, srcV]) cX Bc)
    (hfi : FunAll P fi (.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV])
      (fun w c => Qi w ∧ c ≤ Bi)) :
    FunAll P f (.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV])
      (fun w c => ∃ wI, Qi wI ∧ w = .list [.list [gx, gy, cX, .list []], wI] ∧
        c ≤ itCfIC (Val.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd,
          srcV]).wt Bg Bc Bi) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (Val.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd,
      srcV]).wt := ⟨_, rfl⟩
  rw [← hX]
  have e : (Val.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV]).wt = X :=
    hX.symm
  have ws : (Val.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]).wt < X :=
    hX ▸ wt_le_wt_list (by simp)
  have wsrc : srcV.wt < X := hX ▸ wt_le_wt_list (by simp)
  have wkq : (Val.list [.nat k, .nat q]).wt < (Val.list [sv, .list [.nat k, .nat q], psV, fxV, fyV,
    cv]).wt := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have wfx : fxV.wt < (Val.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]).wt :=
    wt_le_wt_list (by simp)
  have wfy : fyV.wt < (Val.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]).wt :=
    wt_le_wt_list (by simp)
  have wgx := FunDet.wt_lt hgx
  have wgy := FunDet.wt_lt hgy
  have wcX := FunDet.wt_lt hcol
  have hx2 := wt_list2_le (.nat q) fxV
  have hy2 := wt_list2_le (.nat q) fyV
  have hc3 := wt_list3_le (.nat q) gx srcV
  -- `q` from the input, in any environment that starts with it
  have gq : ∀ rest : List Val, Det P (.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv],
      dd, cd, srcV] :: rest) (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.nat q) (10 * (X + 1)) :=
    fun rest => (Det.get' (Det.get' (Det.arg' (P := P) (j := 0) (rest := rest)
      (vs := [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV])
      (v := .list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]) rfl) (Det.nat 1)
      (v := .list [.nat k, .nat q]) (vs := [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]) rfl)
      (Det.nat 1) (v := .nat q) (vs := [.nat k, .nat q]) rfl).mono (by rw [e]; omega)
  have gs : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv][j]? = some v → j ≤ 5 →
      Det P (.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV] :: rest)
        (.get (arg 0) (.nat j)) v (10 * (X + 1)) := by
    intro rest j v hv hj
    have wv : v.wt < (Val.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]).wt :=
      wt_le_wt_list (List.mem_of_getElem? hv)
    exact (Det.get' (Det.arg' (P := P) (j := 0) (rest := rest)
      (vs := [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV])
      (v := .list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv]) rfl) (Det.nat j) hv).mono
      (by rw [e]; omega)
  have d1 := Det.call (Det.mk2 (gq []) (gs [] 3 fxV rfl (by omega))) hgx
  have d2 := Det.call (Det.mk2 (gq [gx]) (gs [gx] 4 fyV rfl (by omega))) hgy
  have d3 := Det.call (Det.mk3 (gq [gx, gy]) (Det.var' (P := P) (i := 1) (v := gx)
      (env := [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV], gx, gy])
      rfl) (Det.arg' (P := P) (j := 3) (rest := [gx, gy])
      (vs := [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV]) (v := srcV) rfl))
    hcol
  refine FunAll.intro hf (EvalAll.letE d1 fun v1 c1 ⟨hv1, hc1⟩ => ?_)
  subst v1
  refine EvalAll.letE d2 fun v2 c2 ⟨hv2, hc2⟩ => ?_
  subst v2
  refine EvalAll.letE d3 fun v3 c3 ⟨hv3, hc3'⟩ => ?_
  subst v3
  refine EvalAll.letE (Ra := fun w c => Qi w ∧ w.wt < Bi ∧ c ≤ 3 * X + 2 * Bi + 10)
    (EvalAll.call_funAll (Det.var' (P := P) (i := 0)
      (v := .list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV])
      (env := [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV], gx, gy,
        cX]) rfl) fun v ca ⟨hv, hca⟩ => by
      subst hv
      exact hfi.wt_lt.mono fun w c ⟨⟨hq, hc⟩, hwc⟩ => ⟨hq, by omega, by rw [e] at hca; omega⟩)
    fun wI c4 ⟨hq, hwI, hc4⟩ => ?_
  set env4 : List Val := [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv], dd, cd, srcV],
    gx, gy, cX, wI] with henv4
  have d5 := Det.mk2 (Det.mk4 (Det.var' (P := P) (env := env4) (i := 1) (v := gx) rfl)
    (Det.var' (P := P) (env := env4) (i := 2) (v := gy) rfl)
    (Det.var' (P := P) (env := env4) (i := 3) (v := cX) rfl) (Det.nil (P := P) (env := env4)))
    (Det.var' (P := P) (env := env4) (i := 4) (v := wI) rfl)
  refine EvalAll.mono d5 fun w c ⟨hw, hc⟩ => ⟨wI, hq, hw, ?_⟩
  have h4 := wt_list4_le gx gy cX (.list [])
  have h2 := wt_list2_le (.list [gx, gy, cX, .list []]) wI
  have hnil := wt_list_nil
  rw [hw]
  unfold itCfIC
  omega

end GI.Impl
