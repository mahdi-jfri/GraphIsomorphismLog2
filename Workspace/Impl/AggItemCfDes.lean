module

public import Workspace.Impl.AggItemCfBin

@[expose] public section

/-!
# Case 3: the objects of a branch

In Case 3 the objects are `designOut d src` and `designOut d' b` (Section A.3, Case 3), with the
colorings `d, d'` of the round. `itCfO3F` computes both with the object stage
(`ItCfObjSpec.des`) on `[K.v, stTv b, wO]` and keeps `wO` (`it_cfO3_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encKColoring)

variable {q : ℕ}

/-- The program of the objects of Case 3, for colorings of arity `κ`. -/
def itCfO3F (fdes κ : ℕ) : Expr :=
  .letE (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1))
  (.letE (.call fdes (mk4 (.var 1) (.nat κ) (.get (.get (arg 0) (.nat 1)) (.nat 0))
      (.get (arg 0) (.nat 3))))
  (.letE (.call fdes (mk4 (.var 1) (.nat κ) (.get (.get (arg 0) (.nat 1)) (.nat 1)) (arg 1)))
    (mk3 (.var 2) (.var 3) (arg 2))))

/-- The cost bound of `itCfO3F`. -/
def itCfO3C (V B : ℕ) : ℕ := 10 ^ 4 * (V + B + 1)

set_option maxHeartbeats 2000000 in
/-- **The objects of Case 3 as a program.** -/
theorem it_cfO3_spec {P : Program} {f fcol forb fdes Co Do κ : ℕ}
    (hf : P.funs[f]? = some (itCfO3F fdes κ)) (hobj : ItCfObjSpec P fcol forb fdes Co Do)
    (sv psV fxV fyV cv code wO : Val) (k : ℕ) {ℓ ℓ' : ℕ} (src : Fin ℓ → Fin q)
    (b : Fin ℓ' → Fin q) (d d' : (Fin κ → Fin q) → ℕ) {V B : ℕ}
    (hV : (Val.list [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv],
      .list [encKColoring d, encKColoring d'], code, stTv src], stTv b, wO]).wt + κ ≤ V)
    (hB1 : itCfB Co Do (itCfDesIn d src).wt ≤ B) (hB2 : itCfB Co Do (itCfDesIn d' b).wt ≤ B) :
    FunDet P f (.list [.list [.list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv],
      .list [encKColoring d, encKColoring d'], code, stTv src], stTv b, wO])
      (.list [itCfOutV (designOut d src), itCfOutV (designOut d' b), wO]) (itCfO3C V B) := by
  set st : Val := .list [sv, .list [.nat k, .nat q], psV, fxV, fyV, cv] with hst
  set dv : Val := .list [encKColoring d, encKColoring d'] with hdv
  set Kv : Val := .list [st, dv, code, stTv src] with hKv
  set x : Val := .list [Kv, stTv b, wO] with hx'
  obtain ⟨W, hW⟩ : ∃ W, W = 100 * (V + B) + 200 := ⟨_, rfl⟩
  have ex : (Val.list [Kv, stTv b, wO]).wt = x.wt := rfl
  have wKv : Kv.wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wtb : (stTv b).wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wwO : wO.wt < x.wt := wt_le_wt_list (by simp [hx'])
  have wst : st.wt < Kv.wt := wt_le_wt_list (by simp [hKv])
  have wdv : dv.wt < Kv.wt := wt_le_wt_list (by simp [hKv])
  have wsrc : (stTv src).wt < Kv.wt := wt_le_wt_list (by simp [hKv])
  have wkq : (Val.list [.nat k, .nat q]).wt < st.wt := wt_le_wt_list (by simp [hst])
  have wq : (Val.nat q).wt < (Val.list [.nat k, .nat q]).wt := wt_le_wt_list (by simp)
  have wd : (encKColoring d).wt < dv.wt := wt_le_wt_list (by simp [hdv])
  have wd' : (encKColoring d').wt < dv.wt := wt_le_wt_list (by simp [hdv])
  have wk := wt_nat_le κ
  have wi1 : (itCfDesIn d src).wt ≤ 8 * V + 8 := by
    unfold itCfDesIn
    have := wt_list4_le (.nat q) (.nat κ) (encKColoring d) (stTv src)
    omega
  have wi2 : (itCfDesIn d' b).wt ≤ 8 * V + 8 := by
    unfold itCfDesIn
    have := wt_list4_le (.nat q) (.nat κ) (encKColoring d') (stTv b)
    omega
  have h1 : FunDet P fdes (itCfDesIn d src) (itCfOutV (designOut d src)) B :=
    (hobj.des d src).mono fun w c h => ⟨h.1, h.2.trans hB1⟩
  have h2 : FunDet P fdes (itCfDesIn d' b) (itCfOutV (designOut d' b)) B :=
    (hobj.des d' b).mono fun w c h => ⟨h.1, h.2.trans hB2⟩
  have wo1 := FunDet.wt_lt h1
  have wo2 := FunDet.wt_lt h2
  have d1 := StDC.get (StDC.get (StDC.get (StDC.arg (P := P) (W := W) (vs := [Kv, stTv b, wO])
      (rest := []) (j := 0) (v := Kv) rfl (by omega) (by omega) (by omega))
      (StDC.nat 0 (by omega)) (v := st) (vs := [st, dv, code, stTv src]) rfl (by omega))
    (StDC.nat 1 (by omega)) (v := .list [.nat k, .nat q]) (vs := [sv, .list [.nat k, .nat q], psV,
      fxV, fyV, cv]) rfl (by omega)) (StDC.nat 1 (by omega)) (v := .nat q) (vs := [.nat k, .nat q])
      rfl (by omega)
  have a2 := StDC.call (StDC.mk4 (W := W) (StDC.var' (P := P) (env := [x, .nat q]) (i := 1)
      (v := .nat q) rfl (by omega)) (StDC.nat κ (by omega))
      (StDC.get (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 0) (v := Kv) rfl
        (by omega) (by omega) (by omega)) (StDC.nat 1 (by omega)) (v := dv)
        (vs := [st, dv, code, stTv src]) rfl (by omega)) (StDC.nat 0 (by omega))
        (v := encKColoring d) (vs := [encKColoring d, encKColoring d']) rfl (by omega))
      (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 0) (v := Kv) rfl
        (by omega) (by omega) (by omega)) (StDC.nat 3 (by omega)) (v := stTv src)
        (vs := [st, dv, code, stTv src]) rfl (by omega))
      (by show (itCfDesIn d src).wt ≤ W; omega) (by omega)) h1 (by omega)
  have a3 := StDC.call (StDC.mk4 (W := W) (StDC.var' (P := P)
      (env := [x, .nat q, itCfOutV (designOut d src)]) (i := 1) (v := .nat q) rfl (by omega))
      (StDC.nat κ (by omega))
      (StDC.get (StDC.get (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 0) (v := Kv) rfl
        (by omega) (by omega) (by omega)) (StDC.nat 1 (by omega)) (v := dv)
        (vs := [st, dv, code, stTv src]) rfl (by omega)) (StDC.nat 1 (by omega))
        (v := encKColoring d') (vs := [encKColoring d, encKColoring d']) rfl (by omega))
      (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 1) (v := stTv b) rfl
        (by omega) (by omega) (by omega))
      (by show (itCfDesIn d' b).wt ≤ W; omega) (by omega)) h2 (by omega)
  have a4 := StDC.mk3 (W := W) (StDC.var' (P := P)
      (env := [x, .nat q, itCfOutV (designOut d src), itCfOutV (designOut d' b)]) (i := 2)
      (v := itCfOutV (designOut d src)) rfl (by omega))
    (StDC.var' (P := P)
      (env := [x, .nat q, itCfOutV (designOut d src), itCfOutV (designOut d' b)]) (i := 3)
      (v := itCfOutV (designOut d' b)) rfl (by omega))
    (StDC.arg (P := P) (vs := [Kv, stTv b, wO]) (j := 2) (v := wO) rfl
        (by omega) (by omega) (by omega))
    (by
      show (Val.list [itCfOutV (designOut d src), itCfOutV (designOut d' b), wO]).wt ≤ W
      have := wt_list3_le (itCfOutV (designOut d src)) (itCfOutV (designOut d' b)) wO
      omega) (by omega)
  have hw3 := wt_list3_le (itCfOutV (designOut d src)) (itCfOutV (designOut d' b)) wO
  refine StDC.funDet hf (StDC.letE d1 (StDC.letE a2 (StDC.letE a3 a4 (by omega)) (by omega))
    (by omega)) ?_
  unfold itCfO3C
  omega

end GI.Impl
