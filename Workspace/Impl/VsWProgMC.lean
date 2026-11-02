import Workspace.Impl.VsWProgAnn

/-!
# Flattening and combining stored matrices as programs

* `vsWFlatFuns b` (8 functions), `vsWFlat_spec`: on `vsWVs M` the flattened `natList M.flatten`.
* `vsWMCFuns b` (31 functions), `vsWMC_spec`: on `[p, D, vsFMatsVal Bm, natList a]` the stored
  matrix `vsWVs (vsWMC p D Bm a)`. Meaning: `GI.Proved.vsWMC_matrix`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-! ### Flattening -/

/-- One step of the flattening, on `[c, acc, row]`: append the row. -/
def vsWFlatStepF (app : ℕ) : Expr := .call app (mk2 (arg 1) (arg 2))

/-- The flattening, on `M`. -/
def vsWFlatF (fo : ℕ) : Expr := .call fo (mk3 .nil (.var 0) .nil)

/-- The flattening program at base `b` (8 functions). -/
def vsWFlatFuns (b : ℕ) : List Expr :=
  [vsWFlatF (b + 1)] ++ foldlFuns (b + 1) (b + 4) ++ [vsWFlatStepF (b + 5)] ++ appendFuns (b + 5)

theorem vsWFlatFuns_length (b : ℕ) : (vsWFlatFuns b).length = 8 := rfl

theorem vsWFlat_take {p D : ℕ} {M : List (List ℕ)} (hM : GI.Proved.VsWSq p D M) (i : ℕ) :
    (∀ y ∈ (M.take i).flatten, y < p) ∧ (M.take i).flatten.length ≤ D * D := by
  have hr : ∀ r ∈ M.take i, r.length = D := fun r hr => (hM.1 r (List.mem_of_mem_take hr)).2
  refine ⟨GI.Proved.vsFA_flatten_lt fun r hr => (hM.1 r (List.mem_of_mem_take hr)).1, ?_⟩
  rw [GI.Proved.vsFA_flatten_length hr, List.length_take, ← hM.2]
  exact Nat.mul_le_mul_right _ (min_le_right _ _)

/-- **The flattening program.** -/
theorem vsWFlat_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWFlatFuns b)) {p N D : ℕ}
    (hpN : p ≤ N) (hDD : D * D ≤ N) {M : List (List ℕ)} (hM : GI.Proved.VsWSq p D M) :
    FunDet P b (vsWVs M) (natList M.flatten) (10 ^ 6 * (N + 1) ^ 4) := by
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  have h0 : P.funs[b]? = some (vsWFlatF (b + 1)) := h.get (j := 0) (by simp [vsWFlatFuns])
  have hfo : P.HasAt (b + 1) (foldlFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsWFlatStepF (b + 5)) :=
    h.get (j := 4) (by rw [vsWFlatFuns_length]; omega)
  have hap : P.HasAt (b + 5) (appendFuns (b + 5)) := h.block 5 rfl
  have hK : loopModK = 1000 := rfl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wF : ∀ i, (natList (M.take i).flatten).wt ≤ 5 * (N + 1) ^ 2 := fun i =>
    wt_natList_le_sq (fun y hy => ((vsWFlat_take hM i).1 y hy).le.trans hpN)
      ((vsWFlat_take hM i).2.trans hDD)
  have hfold := foldl_spec hfo (c := .list []) (xs := M.map natList) (acc0 := .list [])
    (Inv := fun i acc => acc = natList (M.take i).flatten)
    (M := 5 * (N + 1) ^ 2) (B := fun _ => 10 ^ 5 * (N + 1) ^ 3) (by simp [natList])
    (fun i acc _ hacc => by subst hacc; exact wF i)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < M.length := by simpa using hi
      have hx : (M.map natList)[i] = natList M[i] := by simp
      rw [hx]
      have hrow := hM.1 M[i] (List.getElem_mem hi')
      have wFi := wF i
      set F := (M.take i).flatten
      have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.list [], natList F, natList M[i]])
        (j := 1) rfl
      have a2 := Det.arg' (P := P) (rest := []) (vs := [Val.list [], natList F, natList M[i]])
        (j := 2) rfl
      have hF1 : F ++ M[i] = (M.take (i + 1)).flatten := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
          List.flatten_append, List.flatten_singleton]
      have wR := wt_natList_le_sq (B := N) (xs := M[i]) (fun y hy => (hrow.1 y hy).le.trans hpN)
        (by rw [hrow.2]; exact hDN)
      have wF1 := wF (i + 1)
      rw [← hF1] at wF1
      have eF1 : natList (F ++ M[i]) = .list (F.map Val.nat ++ M[i].map Val.nat) := by
        simp [natList]
      have kapp : loopModK * ((M[i].map Val.nat).length + 1) *
          ((Val.list [.list (F.map Val.nat), .list (M[i].map Val.nat)]).wt +
            (M[i].map Val.nat).length + (Val.list (F.map Val.nat ++ M[i].map Val.nat)).wt + 1) ≤
          1000 * (N + 1) * (40 * (N + 1) ^ 2) := by
        have w2 := wt_list2_le (natList F) (natList M[i])
        rw [hK, ← eF1]
        simp only [List.length_map, hrow.2]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
          have : (Val.list [natList F, natList M[i]]).wt =
            (Val.list [.list (F.map Val.nat), .list (M[i].map Val.nat)]).wt := rfl
          omega)
      have dap := Det.call (Det.mk2 a1 a2) ((append_spec hap (F.map Val.nat) (M[i].map Val.nat)).mono
        fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ kapp)⟩)
      refine FunAll.mono (FunDet.intro hst (dap.mono le_rfl)) fun w c hw => ⟨?_, ?_⟩
      · beta_reduce; rw [hw.1, ← hF1, eF1]
      · beta_reduce
        refine hw.2.trans ?_
        have w3 := wt_list3_le (.list []) (natList F) (natList M[i])
        have w2 := wt_list2_le (natList F) (natList M[i])
        have e2 : (Val.list [natList F, natList M[i]]).wt =
          (Val.list [.list (F.map Val.nat), .list (M[i].map Val.nat)]).wt := rfl
        have wn : (Val.list []).wt ≤ 4 := by decide
        have e3 : (1000 * (N + 1) * (40 * (N + 1) ^ 2)) = 40000 * (N + 1) ^ 3 := by ring
        have wo : (Val.list (F.map Val.nat ++ M[i].map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 := by
          rw [← eF1]; exact wF1
        omega)
  refine FunDet.intro h0 ((Det.call (Det.mk3 Det.nil (Det.var' (P := P) (env := [vsWVs M]) (i := 0)
    rfl) Det.nil) (hfold.mono fun w c hw => ⟨by rw [hw.1, List.length_map, List.take_length], hw.2⟩)).mono ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at *
  have wM := wt_vsWVs_le (VsWFit.bnd hM.1 hpN hDN) (show M.length ≤ N + 1 by have := hM.2; omega)
  have eM : (vsWVs M).wt = (Val.list (M.map natList)).wt := rfl
  have w3 := wt_list3_le (.list []) (vsWVs M) (.list [])
  have w3' := wt_list3_le (.list []) (.list (M.map natList)) (.list [])
  have wn : (Val.list []).wt ≤ 4 := by decide
  have wo := wF M.length
  rw [List.take_length] at wo
  have hMl : M.length ≤ N := by have := hM.2; omega
  have k1 : M.length * (10 ^ 5 * (N + 1) ^ 3) ≤ (N + 1) * (10 ^ 5 * (N + 1) ^ 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have k2 : loopModK * (M.length + 1) * ((Val.list [.list [], .list (M.map natList), .list []]).wt +
      M.length + 5 * (N + 1) ^ 2 + 1) ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : (N + 1) * (10 ^ 5 * (N + 1) ^ 3) = 10 ^ 5 * (N + 1) ^ 4 := by ring
  have e2 : 1000 * (N + 1) * (100 * (N + 1) ^ 3) = 10 ^ 5 * (N + 1) ^ 4 := by ring
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ### Combinations of stored matrices -/

theorem vsWVs_injective : Function.Injective vsWVs := by
  intro us ws h
  exact (List.map_injective_iff.mpr vsQ_natList_injective) (Val.list.inj h)

/-- `[r, M] ↦ M[r]`. -/
def vsWGetRowF : Expr := .get (arg 1) (arg 0)

theorem vsWGetRow_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsWGetRowF) {r : ℕ}
    {M : List (List ℕ)} (hr : r < M.length) :
    FunDet P f (.list [.nat r, vsWVs M]) (natList (M.getD r []))
      (10 * ((vsWVs M).wt + r) + 100) := by
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat r, vsWVs M]) (j := 0) rfl
  have a1 : Det P [.list [.nat r, vsWVs M]] (arg 1) (.list (M.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat r, vsWVs M]) (j := 1) rfl
  have hv : (M.map natList)[r]? = some (natList (M.getD r [])) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hr, List.getD_eq_getElem _ _ hr]; rfl
  refine FunDet.intro hf ((Det.get' a1 a0 hv).mono ?_)
  have w1 : (natList (M.getD r [])).wt < (vsWVs M).wt := by
    have := wt_getElem_lt (M.map natList) r (by simpa using hr)
    rw [List.getElem_map, ← List.getD_eq_getElem (d := [])] at this
    exact this
  have w2 := wt_list2_le (.nat r) (vsWVs M)
  have wr := wt_nat_le r
  have eM : (vsWVs M).wt = (Val.list (M.map natList)).wt := rfl
  omega

/-- One row of the combination, on `[[p, Bm, z, a], r]`: combine the rows `r` of the `Bm_i`. -/
def vsWMCItemF (imap row : ℕ) : Expr :=
  .call row (mk2 (mk3 (.get (arg 0) (.nat 0)) (.call imap (mk2 (arg 1) (.get (arg 0) (.nat 1))))
    (.get (arg 0) (.nat 2))) (.get (arg 0) (.nat 3)))

/-- The combination, on `[p, D, Bm, a]`. -/
def vsWMCF (omap rep rng : ℕ) : Expr :=
  .call omap (mk2 (mk4 (arg 0) (arg 2) (.call rep (mk2 (arg 1) (.nat 0))) (arg 3)) (.call rng (arg 1)))

/-- The combination program at base `b` (31 functions). -/
def vsWMCFuns (b : ℕ) : List Expr :=
  [vsWMCF (b + 1) (b + 25) (b + 28)] ++ mapFuns (b + 1) (b + 4) ++ [vsWMCItemF (b + 5) (b + 12)] ++
    mapFuns (b + 5) (b + 8) ++ [vsWGetRowF] ++ vsFMatMulFuns (b + 9) ++ replicateFuns (b + 25) ++
    rangeFuns (b + 28)

theorem vsWMCFuns_length (b : ℕ) : (vsWMCFuns b).length = 31 := rfl

/-- The weight of a list of stored `D × D` matrices. -/
theorem wt_vsWMats_le {p N D : ℕ} (hpN : p ≤ N) (hDN : D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M) (hl : Bm.length ≤ N + 1) :
    (vsFMatsVal Bm).wt ≤ 40 * (N + 1) ^ 4 :=
  wt_vsFMatsVal_le hpN hDN (fun M hM => GI.Proved.vsWSq_vsFSq (hB M hM)) hl

theorem vsWMCItem_spec {P : Program} {f imap row : ℕ} (hf : P.funs[f]? = some (vsWMCItemF imap row))
    (him : P.HasAt imap (mapFuns imap (imap + 3)))
    (hg : P.funs[imap + 3]? = some vsWGetRowF) (hrow : P.funs[row]? = some (vsFRowF (row + 1)))
    (hfo : P.HasAt (row + 1) (foldlFuns (row + 1) (row + 4)))
    (hst : P.funs[row + 4]? = some (vsFMulStepF (row + 5))) (hl : P.HasAt (row + 5) (vsLinFuns (row + 5)))
    {p N D : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hDN : D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M) (hBl : Bm.length ≤ N) {a : List ℕ}
    (ha : ∀ y ∈ a, y < p) (hal : a.length ≤ N) (hBa : Bm.length ≤ a.length) {r : ℕ} (hr : r < D) :
    FunDet P f (.list [.list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a], .nat r])
      (natList (vsFRowMul p a (Bm.map fun M => M.getD r []) (vsWZ D))) (5 * 10 ^ 6 * (N + 1) ^ 5) := by
  set C := Val.list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [C, .nat r]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [C, .nat r]) (j := 1) rfl
  have g k {v : Val} (hv : [Val.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a][k]? = some v) :=
    Det.get' a0 (Det.nat k) hv
  have gB : Det P [.list [C, .nat r]] (.get (arg 0) (.nat 1)) (.list (Bm.map vsWVs)) _ := g 1 rfl
  have wM : ∀ M ∈ Bm, (vsWVs M).wt ≤ 11 * (N + 1) ^ 3 + 4 := fun M hM =>
    wt_vsWVs_le (VsWFit.bnd (hB M hM).1 hpN hDN) (by have := (hB M hM).2; omega)
  have dmap := vsQ_map him Bm vsWVs (fun M => natList (M.getD r [])) vsWVs_injective
    (c := .nat r) (B := 10 * (11 * (N + 1) ^ 3 + 4 + N) + 100) fun M hM =>
      (vsWGetRow_spec hg (by rw [(hB M hM).2]; exact hr)).mono (by have := wM M hM; omega)
  set L := Bm.map fun M => M.getD r []
  have eL : Bm.map (fun M => natList (M.getD r [])) = L.map natList := by simp [L]
  rw [eL] at dmap
  have dL := Det.call (Det.mk2 a1 gB) dmap
  have hLrow : ∀ x ∈ L, (∀ y ∈ x, y < p) ∧ x.length = D := by
    intro x hx
    simp only [L, List.mem_map] at hx
    obtain ⟨M, hM, rfl⟩ := hx
    have hrM : r < M.length := by rw [(hB M hM).2]; exact hr
    rw [List.getD_eq_getElem _ _ hrM]
    exact (hB M hM).1 _ (List.getElem_mem hrM)
  have H : VsFRowFits p N a L (vsWZ D) :=
    ⟨ha, hal, fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
      fun x hx y hy => ((hLrow x hx).1 y hy).le.trans hpN, fun x hx => (hLrow x hx).2.le.trans hDN,
      fun x hx => by simp [vsWZ, (hLrow x hx).2], by simp [L]; omega⟩
  have drow := Det.call (Det.mk2 (Det.mk3 (g 0 rfl) dL (g 2 rfl)) (g 3 rfl))
    (vsFRow_spec hrow hfo hst hl hp hpN H)
  refine FunDet.intro hf (drow.mono ?_)
  have wB := wt_vsWMats_le hpN hDN hB (by omega)
  have eB : (vsFMatsVal Bm).wt = (Val.list (Bm.map vsWVs)).wt := rfl
  have wL := wt_vsWVs_le (N := N) (us := L) (fun x hx => ⟨fun y hy => ((hLrow x hx).1 y hy).le.trans hpN,
    (hLrow x hx).2.le.trans hDN⟩) (by simp [L]; omega)
  have eLv : (vsWVs L).wt = (Val.list (L.map natList)).wt := rfl
  have wz : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wa := wt_natList_le_sq (B := N) (xs := a) (fun y hy => (ha y hy).le.trans hpN) hal
  have wo := wt_natList_le_sq (B := N) (xs := vsFRowMul p a L (vsWZ D))
    (fun y hy => (vsFMulAcc_foldl_lt hp a L (fun y hy => by simp [vsWZ] at hy; omega) y hy).le.trans hpN)
    (by rw [vsFRowMul, vsFMulAcc_foldl_length]; simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wr := wt_nat_le r
  have w4 := wt_list4_le (.nat p) (vsFMatsVal Bm) (natList (vsWZ D)) (natList a)
  have eC : C.wt = (Val.list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a]).wt := rfl
  have w2 := wt_list2_le C (.nat r)
  have w2' := wt_list2_le (.nat r) (.list (Bm.map vsWVs))
  have w3 := wt_list3_le (.nat p) (.list (L.map natList)) (natList (vsWZ D))
  have eCtx : vsFMatCtx p L (vsWZ D) = .list [.nat p, .list (L.map natList), natList (vsWZ D)] := rfl
  have w2'' := wt_list2_le (vsFMatCtx p L (vsWZ D)) (natList a)
  rw [eCtx] at w2''
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := Bm.length) (B := 10 * (11 * (N + 1) ^ 3 + 4 + N) + 100)
    (c := 200) (k := 4) (W := (Val.list [.nat r, .list (Bm.map vsWVs)]).wt +
      (Val.list (L.map natList)).wt) hBl (by omega) (by omega)
  have e5 : (N + 1) ^ (4 + 1) = (N + 1) ^ 5 := rfl
  omega

/-- **The combination program.** -/
theorem vsWMC_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWMCFuns b)) {p N D : ℕ} (hp : 0 < p)
    (hpN : p ≤ N) (hDN : D ≤ N) {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, GI.Proved.VsWSq p D M)
    (hBl : Bm.length ≤ N) {a : List ℕ} (ha : ∀ y ∈ a, y < p) (hal : a.length ≤ N)
    (hBa : Bm.length ≤ a.length) :
    FunDet P b (.list [.nat p, .nat D, vsFMatsVal Bm, natList a]) (vsWVs (vsWMC p D Bm a))
      (10 ^ 10 * (N + 1) ^ 6) := by
  have h0 : P.funs[b]? = some (vsWMCF (b + 1) (b + 25) (b + 28)) :=
    h.get (j := 0) (by simp [vsWMCFuns])
  have hom : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hit : P.funs[b + 4]? = some (vsWMCItemF (b + 5) (b + 12)) :=
    h.get (j := 4) (by rw [vsWMCFuns_length]; omega)
  have him : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)) := h.block 5 rfl
  have hg : P.funs[b + 5 + 3]? = some vsWGetRowF := h.get (j := 8) (by rw [vsWMCFuns_length]; omega)
  have hmm : P.HasAt (b + 9) (vsFMatMulFuns (b + 9)) := h.block 9 rfl
  have hrow : P.funs[b + 12]? = some (vsFRowF (b + 12 + 1)) :=
    hmm.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)
  have hfo : P.HasAt (b + 12 + 1) (foldlFuns (b + 12 + 1) (b + 12 + 4)) := hmm.block 4 rfl
  have hst : P.funs[b + 12 + 4]? = some (vsFMulStepF (b + 12 + 5)) :=
    hmm.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)
  have hl : P.HasAt (b + 12 + 5) (vsLinFuns (b + 12 + 5)) := hmm.block 8 rfl
  have hrep : P.HasAt (b + 25) (replicateFuns (b + 25)) := h.block 25 rfl
  have hrg : P.HasAt (b + 28) (rangeFuns (b + 28)) := h.block 28 rfl
  set X := Val.list [.nat p, .nat D, vsFMatsVal Bm, natList a]
  have ar k {v : Val} (hv : [Val.nat p, .nat D, vsFMatsVal Bm, natList a][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat D, vsFMatsVal Bm, natList a]) (j := k) hv
  have dz := vsWZero_det hrep (ar 1 rfl) hDN
  have drg := Det.call (ar 1 rfl) (vsWRange_det hrg hDN)
  have dmap := vsQ_map hom (List.range D) Val.nat
    (fun r => natList (vsFRowMul p a (Bm.map fun M => M.getD r []) (vsWZ D))) valNat_injective
    (c := .list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a]) fun r hr =>
      vsWMCItem_spec hit him hg hrow hfo hst hl hp hpN hDN hB hBl ha hal hBa (by simpa using hr)
  have e1 : (List.range D).map (fun r => natList (vsFRowMul p a (Bm.map fun M => M.getD r [])
      (vsWZ D))) = (vsWMC p D Bm a).map natList := by simp [vsWMC]
  rw [e1] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 (Det.mk4 (ar 0 rfl) (ar 2 rfl) dz (ar 3 rfl)) drg)
    dmap).mono ?_)
  have hMC := GI.Proved.vsWMC_sq (p := p) (D := D) hp Bm a
  have wO := wt_vsWVs_le (VsWFit.bnd hMC.1 hpN hDN) (show (vsWMC p D Bm a).length ≤ N + 1 by
    rw [hMC.2]; omega)
  have eO : (vsWVs (vsWMC p D Bm a)).wt = (Val.list ((vsWMC p D Bm a).map natList)).wt := rfl
  have wB := wt_vsWMats_le hpN hDN hB (by omega)
  have wz : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wa := wt_natList_le_sq (B := N) (xs := a) (fun y hy => (ha y hy).le.trans hpN) hal
  have wrg := wt_natList_le_sq (B := N) (xs := List.range D) (fun y hy => by simp at hy; omega)
    (by simp; omega)
  have eN : natList (List.range D) = .list ((List.range D).map Val.nat) := rfl
  rw [eN] at wrg
  have wp := wt_nat_le p
  have wd := wt_nat_le D
  have wX := wt_list4_le (.nat p) (.nat D) (vsFMatsVal Bm) (natList a)
  have eX : X.wt = (Val.list [.nat p, .nat D, vsFMatsVal Bm, natList a]).wt := rfl
  have w4 := wt_list4_le (.nat p) (vsFMatsVal Bm) (natList (vsWZ D)) (natList a)
  have w2 := wt_list2_le (.list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a])
    (.list ((List.range D).map Val.nat))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := (List.range D).length) (B := 5 * 10 ^ 6 * (N + 1) ^ 5)
    (c := 5 * 10 ^ 6) (k := 5)
    (W := (Val.list [.list [.nat p, vsFMatsVal Bm, natList (vsWZ D), natList a],
      .list ((List.range D).map Val.nat)]).wt + (Val.list ((vsWMC p D Bm a).map natList)).wt)
    (by simp; omega) le_rfl (by omega)
  have e6 : (N + 1) ^ (5 + 1) = (N + 1) ^ 6 := rfl
  omega

end GI.Impl
