import Workspace.Impl.VsWProgKer

/-!
# Echelon rows, bases and keys as programs

* `vsWRowsFuns b` (34 functions), `vsWRows_spec`: on `[p, vsWVs us]` the rows of the insertion
  of the pairs `(u, [])`.
* `vsWBasFuns b` (38 functions), `vsWBas_spec`: on `[p, vsWVs us]` the basis `vsWBas p us`.
  Meaning: `GI.Proved.vsWBas_span`, `vsWBas_indep`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

theorem vsRowVal_inj : Function.Injective VsRow.val := by
  intro r s h
  simp only [VsRow.val, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  cases r; cases s
  simp only [VsRow.mk.injEq]
  exact ⟨h1, vsQ_natList_injective h2, vsQ_natList_injective h3⟩

/-- `[c, u] ↦ [u, []]`. -/
def vsWMkPairF : Expr := mk2 (arg 1) .nil

/-- `[c, row] ↦ main part of the row`. -/
def vsWRowXF : Expr := .get (arg 1) (.nat 1)

theorem vsWMkPair_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWMkPairF) {N : ℕ}
    (c : Val) (hc : c.wt ≤ 3) {u : List ℕ} (hu : (natList u).wt ≤ 5 * (N + 1) ^ 2) :
    FunDet P f (.list [c, natList u]) (vsPairVal (u, [])) (50 * (N + 1) ^ 2 + 100) := by
  refine FunDet.intro hf ((Det.mk2 (Det.arg' (P := P) (rest := []) (vs := [c, natList u]) (j := 1)
    rfl) Det.nil).mono ?_)
  have := wt_list2_le c (natList u)
  have := wt_list2_le (natList u) (.list [])
  simp only [wt_list_nil] at *
  omega

theorem vsWRowX_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWRowXF) {N : ℕ}
    (c : Val) (hc : c.wt ≤ 3) {r : VsRow} (hr : (r.val).wt ≤ 40 * (N + 1) ^ 2) :
    FunDet P f (.list [c, r.val]) (natList r.x) (200 * (N + 1) ^ 2 + 100) := by
  refine FunDet.intro hf ((Det.get' (Det.arg' (P := P) (rest := []) (vs := [c, r.val]) (j := 1)
    rfl) (Det.nat 1) (show [Val.nat r.j, natList r.x, natList r.t][1]? = some (natList r.x)
      from rfl)).mono ?_)
  have := wt_list2_le c r.val
  have : (natList r.x).wt < r.val.wt := wt_le_wt_list (by simp [VsRow.val])
  omega

/-! ### Rows -/

/-- The rows, on `[p, vs]`. -/
def vsWRowsF (mp ins : ℕ) : Expr :=
  .get (.call ins (mk3 (arg 0) (.call mp (mk2 (.nat 0) (arg 1))) (mk2 .nil .nil))) (.nat 0)

/-- The rows program at base `b` (34 functions). -/
def vsWRowsFuns (b : ℕ) : List Expr :=
  [vsWRowsF (b + 1) (b + 5)] ++ mapFuns (b + 1) (b + 4) ++ [vsWMkPairF] ++ vsInsertAllFuns (b + 5)

theorem vsWRowsFuns_length (b : ℕ) : (vsWRowsFuns b).length = 34 := rfl

theorem wt_vsWPairs_le {p N : ℕ} (hpN : p ≤ N) {us : List (List ℕ)}
    (h : ∀ u ∈ us, (∀ y ∈ u, y < p) ∧ u.length ≤ N) (hl : us.length ≤ N) :
    (Val.list ((vsWPairs us).map vsPairVal)).wt ≤ 100 * (N + 1) ^ 3 := by
  have := vs_wt_list_le_of ((vsWPairs us).map vsPairVal) (c := 20 * (N + 1) ^ 2 + 6) (by
    simp only [vsWPairs, List.map_map, List.mem_map, Function.comp_apply, forall_exists_index,
      and_imp]
    rintro _ u hu rfl
    exact wt_vsPairVal_le hpN (h u hu).1 (by simp) (h u hu).2 (by simp))
  simp only [vsWPairs, List.length_map] at this ⊢
  have e : us.length * (2 * (20 * (N + 1) ^ 2 + 6) + 1) ≤ (N + 1) * (60 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
  have : (N + 1) * (60 * (N + 1) ^ 2) = 60 * (N + 1) ^ 3 := by ring
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem vsWRows_fits {p N d : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) :
    VsAccFits p N d 0 us.length (vsInsertAll p (vsWPairs us)) := by
  have := vsInsertAll_fits hp hpN (L := vsWPairs us) (lx := d) (lt := 0) (fun xt hxt => by
    simp only [vsWPairs, List.mem_map] at hxt
    obtain ⟨u, hu, rfl⟩ := hxt
    exact ⟨⟨(hus u hu).1, by simp, (hus u hu).2.le.trans hdN, by simp⟩, (hus u hu).2, rfl⟩)
  simpa [vsWPairs] using this

/-- **The rows program.** -/
theorem vsWRows_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWRowsFuns b)) {p N d : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) :
    FunDet P b (.list [.nat p, vsWVs us]) (.list ((vsWRows p us).map VsRow.val))
      (4 * 10 ^ 7 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWRowsF (b + 1) (b + 5)) := h.get (j := 0) (by simp [vsWRowsFuns])
  have hm : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hmp : P.funs[b + 4]? = some vsWMkPairF := h.get (j := 4) (by rw [vsWRowsFuns_length]; omega)
  have hin : P.HasAt (b + 5) (vsInsertAllFuns (b + 5)) := h.block 5 rfl
  set A := Val.list [.nat p, vsWVs us]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs us]) (j := 0) rfl
  have a1 : Det P [A] (arg 1) (.list (us.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, vsWVs us]) (j := 1) rfl
  have wu : ∀ u ∈ us, (natList u).wt ≤ 5 * (N + 1) ^ 2 := fun u hu =>
    wt_natList_le_sq (fun y hy => ((hus u hu).1 y hy).le.trans hpN) ((hus u hu).2.le.trans hdN)
  have dmap := vsQ_map hm us natList (fun u => vsPairVal (u, [])) vsQ_natList_injective
    (c := .nat 0) fun u hu => vsWMkPair_spec hmp (.nat 0) (by decide) (wu u hu)
  have e1 : us.map (fun u => vsPairVal (u, [])) = (vsWPairs us).map vsPairVal := by
    simp [vsWPairs]
  rw [e1] at dmap
  have dcall := Det.call (Det.mk2 (Det.nat 0) a1) dmap
  have hL : ∀ xt ∈ vsWPairs us, VsPairFits p N xt ∧ xt.1.length = d ∧ xt.2.length = 0 := by
    intro xt hxt
    simp only [vsWPairs, List.mem_map] at hxt
    obtain ⟨u, hu, rfl⟩ := hxt
    exact ⟨⟨(hus u hu).1, by simp, (hus u hu).2.le.trans hdN, by simp⟩, (hus u hu).2, rfl⟩
  have hLl : (vsWPairs us).length ≤ N := by simp [vsWPairs, hl]
  have dins := Det.call (Det.mk3 a0 dcall (Det.mk2 Det.nil Det.nil))
    (vsInsertAll_spec hin hp hpN hL hLl)
  have dget := Det.get' dins (Det.nat 0) (show [Val.list ((vsInsertAll p (vsWPairs us)).1.map
    VsRow.val), .list ((vsInsertAll p (vsWPairs us)).2.map natList)][0]? =
      some (.list ((vsWRows p us).map VsRow.val)) from rfl)
  refine FunDet.intro h0 (dget.mono ?_)
  have hfit := vsWRows_fits hp hpN hdN hus
  have wacc := wt_vsAccVal_le hpN (by omega) hfit
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wpr := wt_vsWPairs_le hpN (us := us) (fun u hu => ⟨(hus u hu).1, (hus u hu).2.le.trans hdN⟩) hl
  have wrows := wt_vsRows_le hfit.rows (hfit.nrows.trans (by omega))
  have wp := wt_nat_le p
  have wA := wt_list2_le (.nat p) (vsWVs us)
  have w2 := wt_list2_le (.nat 0) (.list (us.map natList))
  have w3 := wt_list3_le (.nat p) (.list ((vsWPairs us).map vsPairVal)) (.list [.list [], .list []])
  have wn : (Val.list [Val.list [], Val.list []]).wt ≤ 20 := by decide
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : mapK = 1000 := rfl
  have w00 := wt_nat_le 0
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have kmap : us.length * (50 * (N + 1) ^ 2 + 100) ≤ (N + 1) * (150 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have kmap2 : mapK * (us.length + 1) * ((Val.list [.nat 0, .list (us.map natList)]).wt +
      (Val.list ((vsWPairs us).map vsPairVal)).wt + 1) ≤ 1000 * (N + 1) * (200 * (N + 1) ^ 3) := by
    rw [hK]
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    have : (vsWVs us).wt = (Val.list (us.map natList)).wt := rfl
    omega
  have e3 : (N + 1) * (150 * (N + 1) ^ 2) = 150 * (N + 1) ^ 3 := by ring
  have e4 : 1000 * (N + 1) * (200 * (N + 1) ^ 3) = 200000 * (N + 1) ^ 4 := by ring
  have eA : A.wt = (Val.list [.nat p, vsWVs us]).wt := rfl
  have eU : (vsWVs us).wt = (Val.list (us.map natList)).wt := rfl
  have eAcc : (vsAccVal (vsInsertAll p (vsWPairs us))).wt =
    (Val.list [Val.list ((vsInsertAll p (vsWPairs us)).1.map VsRow.val),
      .list ((vsInsertAll p (vsWPairs us)).2.map natList)]).wt := rfl
  have eAcc0 : vsAccVal ([], []) = Val.list [.list [], .list []] := rfl
  have eR : vsWRows p us = (vsInsertAll p (vsWPairs us)).1 := rfl
  simp only [eAcc0, eR] at *
  omega

/-! ### The basis -/

/-- The basis, on `[p, vs]`. -/
def vsWBasF (rows mp : ℕ) : Expr := .call mp (mk2 (.nat 0) (.call rows (.var 0)))

/-- The basis program at base `b` (39 functions). -/
def vsWBasFuns (b : ℕ) : List Expr :=
  [vsWBasF (b + 1) (b + 35)] ++ vsWRowsFuns (b + 1) ++ mapFuns (b + 35) (b + 38) ++ [vsWRowXF]

theorem vsWBasFuns_length (b : ℕ) : (vsWBasFuns b).length = 39 := rfl

theorem wt_rowVal_fits {N lx lt : ℕ} {r : VsRow} (h : VsRowFits N lx lt r) :
    r.val.wt ≤ 40 * (N + 1) ^ 2 := wt_vsRowVal_le h.hrx h.hrt h.lrx h.lrt h.j

/-- **The basis program.** -/
theorem vsWBas_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWBasFuns b)) {p N d : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) :
    FunDet P b (.list [.nat p, vsWVs us]) (vsWVs (vsWBas p us)) (5 * 10 ^ 7 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWBasF (b + 1) (b + 35)) := h.get (j := 0) (by simp [vsWBasFuns])
  have hr : P.HasAt (b + 1) (vsWRowsFuns (b + 1)) := h.block 1 rfl
  have hm : P.HasAt (b + 35) (mapFuns (b + 35) (b + 38)) := h.block 35 rfl
  have hx : P.funs[b + 38]? = some vsWRowXF := h.get (j := 38) (by rw [vsWBasFuns_length]; omega)
  set A := Val.list [.nat p, vsWVs us]
  have hfit := vsWRows_fits hp hpN hdN hus
  have dr := Det.call (Det.var' (P := P) (env := [A]) (i := 0) rfl) (vsWRows_spec hr hp hpN hdN hus hl)
  have dmap := vsQ_map hm (vsWRows p us) VsRow.val (fun r => natList r.x) vsRowVal_inj
    (c := .nat 0) fun r hr' => vsWRowX_spec hx (.nat 0) (by decide) (wt_rowVal_fits (hfit.rows r hr'))
  have e1 : (vsWRows p us).map (fun r => natList r.x) = (vsWBas p us).map natList := by
    simp [vsWBas]
  rw [e1] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 (Det.nat 0) dr) dmap).mono ?_)
  have wrows := wt_vsRows_le hfit.rows (hfit.nrows.trans (by omega))
  have eR : vsWRows p us = (vsInsertAll p (vsWPairs us)).1 := rfl
  rw [← eR] at wrows
  have hbfit := GI.Proved.vsWBas_fit hp hus
  have wbas := wt_vsWVs_le (VsWFit.bnd hbfit hpN hdN) (by
    have : (vsWBas p us).length ≤ us.length := by
      simp only [vsWBas, List.length_map]; exact hfit.nrows
    omega)
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wp := wt_nat_le p
  have w00 := wt_nat_le 0
  have wA := wt_list2_le (.nat p) (vsWVs us)
  have w2 := wt_list2_le (.nat 0) (.list ((vsWRows p us).map VsRow.val))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : mapK = 1000 := rfl
  have hnr : (vsWRows p us).length ≤ N := (eR ▸ hfit.nrows).trans hl
  have kmap : (vsWRows p us).length * (200 * (N + 1) ^ 2 + 100) ≤ (N + 1) * (300 * (N + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have eB : (vsWVs (vsWBas p us)).wt = (Val.list ((vsWBas p us).map natList)).wt := rfl
  have kmap2 : mapK * ((vsWRows p us).length + 1) * ((Val.list [.nat 0,
      .list ((vsWRows p us).map VsRow.val)]).wt + (Val.list ((vsWBas p us).map natList)).wt + 1) ≤
      1000 * (N + 1) * (300 * (N + 1) ^ 3) := by
    rw [hK]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e3 : (N + 1) * (300 * (N + 1) ^ 2) = 300 * (N + 1) ^ 3 := by ring
  have e4 : 1000 * (N + 1) * (300 * (N + 1) ^ 3) = 300000 * (N + 1) ^ 4 := by ring
  have eA : A.wt = (Val.list [.nat p, vsWVs us]).wt := rfl
  omega

end GI.Impl
