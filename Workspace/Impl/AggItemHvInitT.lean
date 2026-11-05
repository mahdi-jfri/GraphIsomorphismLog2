module

public import Workspace.Impl.AggItemHvInitM

@[expose] public section

/-!
# Case 2a init program, part 4: the test of the halving item

The init program first decides the test of `halvingItem`: `|Φ| = |Φ'|` and `|Φ| ≥ 2`, for the
dominant sets `Φ` of `X` and `Φ'` of `Y`. It computes the groups of the second parts of `fx` and
`fy` (`it_grp_spec`) and their sorted dominant sets (`it_dom_spec`), in `itHvPreF`
(`it_hvPre_spec`). If the test fails, the kept value is `[0]`. Otherwise it runs the middle
part `itHvMF` on `[st, Px, Py]`. This is `itHvIF` (`it_hvI_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts gens encGroup)

variable {k q : ℕ}

/-- The test value: `1` if `a = b` and `1 < a`, else `0`. -/
def itHvTv (a b : ℕ) : ℕ := (if a = b then 1 else 0) * (if 1 < a then 1 else 0)

theorem itHvTv_ne_zero {a b : ℕ} : itHvTv a b ≠ 0 ↔ a = b ∧ 2 ≤ a := by
  unfold itHvTv
  by_cases h1 : a = b <;> by_cases h2 : 1 < a <;> simp [h1, h2] <;> omega

theorem itHvTv_le (a b : ℕ) : itHvTv a b ≤ 1 := by
  unfold itHvTv; split_ifs <;> omega

/-- On `[st, dd, code, src]` with `st = [sv, [k, q], ps, fx, fy, cv]`: `[st, Px, Py, test]`. -/
def itHvPreF (grp dom : ℕ) : Expr :=
  .letE (arg 0)
  (.letE (.get (.get (.var 1) (.nat 1)) (.nat 1))
  (.letE (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 3))))
  (.letE (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 4))))
  (.letE (.call dom (.var 3))
  (.letE (.call dom (.var 4))
    (mk4 (.var 1) (.var 5) (.var 6) (.arith .mul (.arith .eq (.length (.var 5)) (.length (.var 6)))
      (.arith .lt (.nat 1) (.length (.var 5))))))))))

/-- The cost bound of `itHvPreF`, from the costs of the callees. -/
def itHvPreC (V cG cD : ℕ) : ℕ := 1000 * (V + cG + cD + 10)

set_option maxHeartbeats 2000000 in
/-- **The test of the halving item as a program.** -/
theorem it_hvPre_spec {P : Program} {f grp dom : ℕ} (hf : P.funs[f]? = some (itHvPreF grp dom))
    (sv psV cv dd cd sr : Val) (fx fy : List (Perm (Fin k) × Perm (Fin q)))
    (Φ Φ' : Finset (Fin q)) (gx gy : Val) {cG cD : ℕ}
    (hgx : FunDet P grp (.list [.nat q, .list (fx.map pairV)]) gx cG)
    (hgy : FunDet P grp (.list [.nat q, .list (fy.map pairV)]) gy cG)
    (hdx : FunDet P dom gx (encPts (Φ.sort (· ≤ ·))) cD)
    (hdy : FunDet P dom gy (encPts (Φ'.sort (· ≤ ·))) cD) {V : ℕ}
    (hV : (Val.list [.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
      .list (fy.map pairV), cv], dd, cd, sr]).wt ≤ V) (hqV : q ≤ V) :
    FunDet P f (.list [.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV),
      .list (fy.map pairV), cv], dd, cd, sr])
      (.list [.list [sv, .list [.nat k, .nat q], psV, .list (fx.map pairV), .list (fy.map pairV),
        cv], encPts (Φ.sort (· ≤ ·)), encPts (Φ'.sort (· ≤ ·)), .nat (itHvTv Φ.card Φ'.card)])
      (itHvPreC V cG cD) := by
  set kq : Val := .list [.nat k, .nat q] with hkq
  set fxV := Val.list (fx.map pairV) with hfxV
  set fyV := Val.list (fy.map pairV) with hfyV
  set st := Val.list [sv, kq, psV, fxV, fyV, cv] with hst
  set v := Val.list [st, dd, cd, sr] with hv
  set Px := encPts (Φ.sort (· ≤ ·)) with hPx
  set Py := encPts (Φ'.sort (· ≤ ·)) with hPy
  have ev : (Val.list [st, dd, cd, sr]).wt = v.wt := rfl
  have est : (Val.list [sv, kq, psV, fxV, fyV, cv]).wt = st.wt := rfl
  have ekq : (Val.list [.nat k, .nat q]).wt = kq.wt := rfl
  have wst : st.wt < v.wt := wt_le_wt_list (by simp)
  have wkq : kq.wt < st.wt := wt_le_wt_list (by simp)
  have wfx : fxV.wt < st.wt := wt_le_wt_list (by simp)
  have wfy : fyV.wt < st.wt := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < kq.wt := wt_le_wt_list (by simp)
  have wgx := FunDet.wt_lt hgx
  have wgy := FunDet.wt_lt hgy
  have wPx := FunDet.wt_lt hdx
  have wPy := FunDet.wt_lt hdy
  set X := V + cG + cD + 10 with hX
  set W := 10 * X + 10 with hW
  have lP : ∀ Ψ : Finset (Fin q), encPts (Ψ.sort (· ≤ ·)) =
      .list (((Ψ.sort (· ≤ ·)).map Fin.val).map Val.nat) := fun Ψ => by
    rw [itHv_encPts]; rfl
  have hlen : ∀ Ψ : Finset (Fin q), (((Ψ.sort (· ≤ ·)).map Fin.val).map Val.nat).length = Ψ.card :=
    fun Ψ => by simp
  have cx : Φ.card < Px.wt := by
    have h := length_lt_wt_list (((Φ.sort (· ≤ ·)).map Fin.val).map Val.nat)
    rw [hlen] at h; rw [hPx, lP]; exact h
  have cy : Φ'.card < Py.wt := by
    have h := length_lt_wt_list (((Φ'.sort (· ≤ ·)).map Fin.val).map Val.nat)
    rw [hlen] at h; rw [hPy, lP]; exact h
  -- the chain
  have d1 : StDC P [v] (arg 0) st 3 0 W :=
    StDC.arg (vs := [st, dd, cd, sr]) rfl (by omega) (by omega) (by omega)
  have d2 : StDC P [v, st] (.get (.get (.var 1) (.nat 1)) (.nat 1)) (.nat q) 5 0 W :=
    StDC.get (StDC.get (vs := [sv, kq, psV, fxV, fyV, cv]) (StDC.var' (v := st) rfl (by omega))
      (StDC.nat 1 (by omega)) rfl (by omega)) (StDC.nat 1 (by omega)) rfl (by omega)
  have d3 : StDC P [v, st, .nat q] (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 3)))) gx 8 cG W :=
    (StDC.call (StDC.mk2 (StDC.var' (W := W) (v := .nat q) rfl (by omega))
      (StDC.get (vs := [sv, kq, psV, fxV, fyV, cv]) (StDC.var' (v := st) rfl (by omega))
        (StDC.nat 3 (by omega)) (v := fxV) rfl (by omega))
      (by have := wt_list2_le (.nat q) fxV; omega) (by omega)) hgx (by omega)).mono (by omega) (by omega)
  have d4 : StDC P [v, st, .nat q, gx] (.call grp (mk2 (.var 2) (.get (.var 1) (.nat 4)))) gy 8 cG
      W :=
    (StDC.call (StDC.mk2 (StDC.var' (W := W) (v := .nat q) rfl (by omega))
      (StDC.get (vs := [sv, kq, psV, fxV, fyV, cv]) (StDC.var' (v := st) rfl (by omega))
        (StDC.nat 4 (by omega)) (v := fyV) rfl (by omega))
      (by have := wt_list2_le (.nat q) fyV; omega) (by omega)) hgy (by omega)).mono (by omega) (by omega)
  have d5 : StDC P [v, st, .nat q, gx, gy] (.call dom (.var 3)) Px 2 cD W :=
    (StDC.call (StDC.var' rfl (by omega)) hdx (by omega)).mono (by omega) (by omega)
  have d6 : StDC P [v, st, .nat q, gx, gy, Px] (.call dom (.var 4)) Py 2 cD W :=
    (StDC.call (StDC.var' rfl (by omega)) hdy (by omega)).mono (by omega) (by omega)
  have ln : ∀ (i : ℕ) (Ψ : Finset (Fin q)) (u : Val), u = encPts (Ψ.sort (· ≤ ·)) → u.wt ≤ W →
      [v, st, .nat q, gx, gy, Px, Py][i]? = some u →
      StDC P [v, st, .nat q, gx, gy, Px, Py] (.length (.var i)) (.nat Ψ.card) 2 0 W := by
    intro i Ψ u hu huw hi
    have hΨ := Ψ.card_le_univ
    rw [Fintype.card_fin] at hΨ
    have h := StDC.length (StDC.var' (P := P) (W := W) (v := .list
      (((Ψ.sort (· ≤ ·)).map Fin.val).map Val.nat)) (by rw [hi, hu, lP])
        (by rw [← lP, ← hu]; exact huw)) (by rw [hlen]; omega)
    rw [hlen] at h
    exact h
  have hT : itHvTv Φ.card Φ'.card ≤ 1 := itHvTv_le _ _
  have d7 : StDC P [v, st, .nat q, gx, gy, Px, Py]
      (mk4 (.var 1) (.var 5) (.var 6) (.arith .mul (.arith .eq (.length (.var 5)) (.length (.var 6)))
        (.arith .lt (.nat 1) (.length (.var 5)))))
      (.list [st, Px, Py, .nat (itHvTv Φ.card Φ'.card)]) 20 0 W := by
    have l5 := ln 5 Φ Px rfl (by omega) rfl
    have l6 := ln 6 Φ' Py rfl (by omega) rfl
    have deq := StDC.arith' (op := .eq) (z := if Φ.card = Φ'.card then 1 else 0) l5 l6 rfl
      (by split_ifs <;> omega)
    have dlt := StDC.arith' (op := .lt) (z := if 1 < Φ.card then 1 else 0)
      (StDC.nat 1 (by omega)) l5 rfl (by split_ifs <;> omega)
    have dmul := StDC.arith' (op := .mul) (z := itHvTv Φ.card Φ'.card) deq dlt rfl (by omega)
    have h4 := wt_list4_le st Px Py (.nat (itHvTv Φ.card Φ'.card))
    have := wt_nat_le (itHvTv Φ.card Φ'.card)
    exact (StDC.mk4 (StDC.var' rfl (by omega)) (StDC.var' rfl (by omega))
      (StDC.var' rfl (by omega)) dmul (by omega) (by omega)).mono (by omega) le_rfl
  have hout : (Val.list [st, Px, Py, .nat (itHvTv Φ.card Φ'.card)]).wt ≤ W := by
    have h4 := wt_list4_le st Px Py (.nat (itHvTv Φ.card Φ'.card))
    have := wt_nat_le (itHvTv Φ.card Φ'.card)
    omega
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 (StDC.letE d5
    (StDC.letE d6 d7 hout) hout) hout) hout) hout) hout
  refine StDC.funDet hf dall ?_
  unfold itHvPreC
  omega

/-- The init program of Case 2a: the test, then the middle part, or `[0]`. -/
def itHvIF (pre m : ℕ) : Expr :=
  .letE (.call pre (.var 0))
    (.ite (.get (.var 1) (.nat 3))
      (.call m (mk3 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 2))))
      (mk1 (.nat 0)))

/-- The cost bound of `itHvIF`, from the costs of its two parts. -/
def itHvIC (V cP cM : ℕ) : ℕ := 4 * cM + 1000 * (V + cP + 10)

set_option maxHeartbeats 2000000 in
/-- **The init program of Case 2a, from its parts.** -/
theorem it_hvI_spec {P : Program} {f pre m : ℕ} (hf : P.funs[f]? = some (itHvIF pre m))
    (v st Px Py : Val) (tv : ℕ) {cP cM : ℕ} {Qm : Val → Prop}
    (hpre : FunDet P pre v (.list [st, Px, Py, .nat tv]) cP)
    (hm : tv ≠ 0 → FunAll P m (.list [st, Px, Py]) (fun w c => Qm w ∧ c ≤ cM)) :
    FunAll P f v (fun w c => ((tv = 0 ∧ w = .list [.nat 0]) ∨ (tv ≠ 0 ∧ Qm w)) ∧
      c ≤ itHvIC v.wt cP cM) := by
  set D := Val.list [st, Px, Py, .nat tv] with hD
  have eD : (Val.list [st, Px, Py, .nat tv]).wt = D.wt := rfl
  have wD : D.wt < cP := FunDet.wt_lt hpre
  have wst : st.wt < D.wt := wt_le_wt_list (by simp)
  have wPx : Px.wt < D.wt := wt_le_wt_list (by simp)
  have wPy : Py.wt < D.wt := wt_le_wt_list (by simp)
  have wtv : (Val.nat tv).wt < D.wt := wt_le_wt_list (by simp)
  set W := 10 * cP + 10 with hW
  have d1 : Det P [v] (.call pre (.var 0)) D (v.wt + 1 + cP + D.wt + 1) :=
    Det.call (Det.var' rfl) hpre
  refine FunAll.intro hf (EvalAll.letE d1 fun u ca h1 => ?_)
  obtain ⟨rfl, hca⟩ := h1
  have dt : StDC P [v, D] (.get (.var 1) (.nat 3)) (.nat tv) 3 0 W :=
    StDC.get (StDC.var' rfl (by omega)) (StDC.nat 3 (by omega)) rfl (by omega)
  refine EvalAll.ite dt.det (fun _ _ h => ⟨tv, h.1⟩) fun x cc h => ?_
  obtain ⟨hx, hcc⟩ := h
  cases hx
  by_cases h0 : tv = 0
  · rw [if_pos h0]
    have hw1 := wt_list1_le (.nat 0)
    have hw0 := wt_nat_le 0
    refine ((Det.mk1 (Det.nat 0)).post fun c' hc' => ?_)
    refine ⟨Or.inl ⟨h0, rfl⟩, ?_⟩
    unfold itHvIC
    omega
  · rw [if_neg h0]
    have da : StDC P [v, D] (mk3 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))
        (.get (.var 1) (.nat 2))) (.list [st, Px, Py]) 13 0 W := by
      have h3 := wt_list3_le st Px Py
      exact (StDC.mk3 (StDC.get (StDC.var' rfl (by omega)) (StDC.nat 0 (by omega)) rfl (by omega))
        (StDC.get (StDC.var' rfl (by omega)) (StDC.nat 1 (by omega)) rfl (by omega))
        (StDC.get (StDC.var' rfl (by omega)) (StDC.nat 2 (by omega)) rfl (by omega))
        (by omega) (by omega)).mono (by omega) le_rfl
    refine EvalAll.call_funAll da.det fun u ca' h2 => ?_
    obtain ⟨rfl, hca'⟩ := h2
    refine ((hm h0).wt_lt).mono fun w cb ⟨⟨hq, hc⟩, hwt⟩ => ⟨Or.inr ⟨h0, hq⟩, ?_⟩
    unfold itHvIC
    omega

end GI.Impl
