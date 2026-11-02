import Workspace.Impl.AggRectRepDW

/-!
# The tests and lookups of the representation program

Each test computes a bit at cost linear in the weight of its input. The bits are the Boolean
tests of `rcRKeyN`, `rcRLook`, `rcRLook1`, `rcRLook2`, the base points and the small labels.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-! ### Bits -/

theorem rcR_eqT (a b : ℕ) : BinOp.eval .eq a b = (a == b).toNat := by
  simp only [BinOp.eval]
  by_cases h : a = b
  · subst h; simp
  · have : (a == b) = false := by simpa using h
    rw [if_neg h, this]; rfl

theorem rcR_notT (b : Bool) : BinOp.eval .eq b.toNat 0 = (!b).toNat := by cases b <;> rfl

theorem rcR_andT (a b : Bool) : BinOp.eval .mul a.toNat b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

theorem rcR_ltT (a b : ℕ) : BinOp.eval .lt a b = (decide (a < b)).toNat := by
  simp only [BinOp.eval]; by_cases h : a < b <;> simp [h]

theorem rcR_wt_toNat (b : Bool) {W : ℕ} (hW : 3 ≤ W) : (Val.nat b.toNat).wt ≤ W :=
  rcR_wt_bitW (by cases b <;> simp) hW

theorem rcR_getD_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) (i : ℕ) : l.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => simp
  | some y => exact h y (List.mem_of_getElem? hx)

theorem rcR_wt_getD_le (l : List ℕ) (i : ℕ) : (Val.nat (l.getD i 0)).wt ≤ (natList l).wt := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => have := wt_nat_le 0; have : 4 ≤ (natList l).wt := by
              rw [natList, wt_list_eq]; omega
            simp; omega
  | some y =>
    simp only [Option.getD_some]
    exact (wt_le_wt_list (List.mem_map.2 ⟨y, List.mem_of_getElem? hx, rfl⟩)).le

/-! ### The tests -/

section Tests

variable {P : Program} {I : RcRIdx}

/-- **The test of the second base point**: `j ∈ W` and `j ≠ w₀`. -/
theorem rcR_w1P_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.w1P]? = some I.w1PF)
    (wl : List ℕ) (w₀ j : ℕ) :
    FunDet P I.w1P (.list [.list [natList wl, .nat w₀], .nat j])
      (boolVal (wl.getD j 0 == 1 && !(j == w₀)))
      (5000 * ((Val.list [.list [natList wl, .nat w₀], .nat j]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList wl, .nat w₀], .nat j]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have hC : (Val.list [natList wl, .nat w₀]).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList wl, .nat w₀], .nat j]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList wl, .nat w₀], .nat j]) (W := W) (j := 1) (v := .nat j) (by omega) rfl
  have gw := rcRDW.get a0 (j := 0) (v := natList wl) rfl
  have gw0 := rcRDW.get a0 (j := 1) (v := .nat w₀) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList wl, .nat w₀], .nat j]]) 0
    (by omega)
  have n1 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList wl, .nat w₀], .nat j]]) 1
    (by omega)
  have g := rcRDW.gdN I hgD gw a1 n0
  have e1 := rcRDW.arith (op := .eq) g n1 rfl (rcR_eval_eq_wt _ _ (by omega))
  have e2 := rcRDW.arith (op := .eq) a1 gw0 rfl (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1 e2
  have e3 := rcRDW.arith (op := .eq) e2 n0 (rcR_notT _) (rcR_wt_toNat _ (by omega))
  have e4 := rcRDW.arith (op := .mul) e1 e3 (rcR_andT _ _) (rcR_wt_toNat _ (by omega))
  exact (rcRDW.fn hf e4).mono (by omega)

/-- **The key test**: `j` in the domain with row label `rli`. -/
theorem rcR_keyP_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.keyP]? = some I.keyPF)
    (dl rl : List ℕ) (rli j : ℕ) :
    FunDet P I.keyP (.list [.list [natList dl, natList rl, .nat rli], .nat j])
      (boolVal (dl.getD j 0 == 1 && rl.getD j 0 == rli))
      (5000 * ((Val.list [.list [natList dl, natList rl, .nat rli], .nat j]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList dl, natList rl, .nat rli], .nat j]).wt :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have hC : (Val.list [natList dl, natList rl, .nat rli]).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList dl, natList rl, .nat rli], .nat j]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList dl, natList rl, .nat rli], .nat j]) (W := W) (j := 1) (v := .nat j) (by omega) rfl
  have gd0 := rcRDW.get a0 (j := 0) (v := natList dl) rfl
  have gr := rcRDW.get a0 (j := 1) (v := natList rl) rfl
  have gli := rcRDW.get a0 (j := 2) (v := .nat rli) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList dl, natList rl, .nat rli], .nat j]])
    0 (by omega)
  have n1 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList dl, natList rl, .nat rli], .nat j]])
    1 (by omega)
  have e1 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD gd0 a1 n0) n1 rfl
    (rcR_eval_eq_wt _ _ (by omega))
  have e2 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD gr a1 n0) gli rfl
    (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1 e2
  have e4 := rcRDW.arith (op := .mul) e1 e2 (rcR_andT _ _) (rcR_wt_toNat _ (by omega))
  exact (rcRDW.fn hf e4).mono (by omega)

/-- **The head test** of `rcRLook`. -/
theorem rcR_lk0P_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.lk0P]? = some I.lk0PF)
    (i : ℕ) (y : List ℕ) :
    FunDet P I.lk0P (.list [.nat i, natList y]) (boolVal (y.getD 0 0 == i))
      (5000 * ((Val.list [.nat i, natList y]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.nat i, natList y]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.nat i, natList y]) (W := W) (j := 0) (v := .nat i) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.nat i, natList y]) (W := W) (j := 1) (v := natList y) (by omega) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.nat i, natList y]]) 0 (by omega)
  have e1 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD a1 n0 n0) a0 rfl
    (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1
  exact (rcRDW.fn hf e1).mono (by omega)

/-- **The first-label test** of `rcRLook1`. -/
theorem rcR_lk1P_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.lk1P]? = some I.lk1PF)
    (t : ℕ) (y : List ℕ) :
    FunDet P I.lk1P (.list [.nat t, natList y]) (boolVal (y.getD 1 0 == t))
      (5000 * ((Val.list [.nat t, natList y]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.nat t, natList y]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.nat t, natList y]) (W := W) (j := 0) (v := .nat t) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.nat t, natList y]) (W := W) (j := 1) (v := natList y) (by omega) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.nat t, natList y]]) 0 (by omega)
  have n1 := rcRDW.nat (P := P) (W := W) (env := [.list [.nat t, natList y]]) 1 (by omega)
  have e1 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD a1 n1 n0) a0 rfl
    (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1
  exact (rcRDW.fn hf e1).mono (by omega)

/-- **The test** of `rcRLook2`. -/
theorem rcR_lk2P_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.lk2P]? = some I.lk2PF)
    (t a : ℕ) (y : List ℕ) :
    FunDet P I.lk2P (.list [.list [.nat t, .nat a], natList y])
      (boolVal (y.getD 1 0 == t && !(y.getD 2 0 == a)))
      (5000 * ((Val.list [.list [.nat t, .nat a], natList y]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [.nat t, .nat a], natList y]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have hC : (Val.list [.nat t, .nat a]).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [.nat t, .nat a], natList y]) (W := W) (j := 0) (v := .list [.nat t, .nat a]) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [.nat t, .nat a], natList y]) (W := W) (j := 1) (v := natList y) (by omega) rfl
  have gt := rcRDW.get a0 (j := 0) (v := .nat t) rfl
  have ga := rcRDW.get a0 (j := 1) (v := .nat a) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [.nat t, .nat a], natList y]]) 0 (by omega)
  have n1 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [.nat t, .nat a], natList y]]) 1 (by omega)
  have n2 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [.nat t, .nat a], natList y]]) 2 (by omega)
  have e1 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD a1 n1 n0) gt rfl
    (rcR_eval_eq_wt _ _ (by omega))
  have e2 := rcRDW.arith (op := .eq) (rcRDW.gdN I hgD a1 n2 n0) ga rfl
    (rcR_eval_eq_wt _ _ (by omega))
  rw [rcR_eqT] at e1 e2
  have e3 := rcRDW.arith (op := .eq) e2 n0 (rcR_notT _) (rcR_wt_toNat _ (by omega))
  have e4 := rcRDW.arith (op := .mul) e1 e3 (rcR_andT _ _) (rcR_wt_toNat _ (by omega))
  exact (rcRDW.fn hf e4).mono (by omega)

/-- **The row embedding** at one row: `σ j` for `j < q`, else `j`. -/
theorem rcR_embR_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.embRF]? = some I.embRFF)
    (σl : List ℕ) (q j : ℕ) :
    FunDet P I.embRF (.list [.list [natList σl, .nat q], .nat j])
      (.nat (if j < q then σl.getD j 0 else j))
      (5000 * ((Val.list [.list [natList σl, .nat q], .nat j]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = (Val.list [.list [natList σl, .nat q], .nat j]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have hC : (Val.list [natList σl, .nat q]).wt < V := by rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList σl, .nat q], .nat j]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList σl, .nat q], .nat j]) (W := W) (j := 1) (v := .nat j) (by omega) rfl
  have gs := rcRDW.get a0 (j := 0) (v := natList σl) rfl
  have gq := rcRDW.get a0 (j := 1) (v := .nat q) rfl
  have n0 := rcRDW.nat (P := P) (W := W) (env := [.list [.list [natList σl, .nat q], .nat j]]) 0 (by omega)
  have e1 := rcRDW.arith (op := .lt) a1 gq rfl (rcR_eval_lt_wt _ _ (by omega))
  have g := rcRDW.gdN I hgD gs a1 n0
  by_cases hj : j < q
  · rw [if_pos hj]
    have e : BinOp.eval .lt j q = 1 := by simp [BinOp.eval, hj]
    rw [e] at e1
    exact (rcRDW.fn hf (rcRDW.ite_pos e1 one_ne_zero g)).mono (by omega)
  · rw [if_neg hj]
    have e : BinOp.eval .lt j q = 0 := by simp [BinOp.eval, hj]
    rw [e] at e1
    exact (rcRDW.fn hf (rcRDW.ite_zero e1 a1)).mono (by omega)

/-- **The row action** at one row: the row of `h` at the key of row `r`. -/
theorem rcR_rho_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.rhoF]? = some I.rhoFF)
    (rowT keys hl : List ℕ) (r : ℕ) :
    FunDet P I.rhoF (.list [.list [natList rowT, natList keys, natList hl], .nat r])
      (.nat (rowT.getD (hl.getD (keys.getD r 0) 0) 0))
      (20000 * ((Val.list [.list [natList rowT, natList keys, natList hl], .nat r]).wt + 10)) := by
  obtain ⟨V, hV⟩ : ∃ V, V =
      (Val.list [.list [natList rowT, natList keys, natList hl], .nat r]).wt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * V + 100 := ⟨_, rfl⟩
  have hC : (Val.list [natList rowT, natList keys, natList hl]).wt < V :=
    by rw [hV]; exact wt_le_wt_list (by simp)
  have a0 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList rowT, natList keys, natList hl], .nat r]) (W := W) (j := 0) (by omega) rfl
  have a1 := rcRDW.arg (P := P) (rest := []) (vs := [.list [natList rowT, natList keys, natList hl], .nat r]) (W := W) (j := 1) (v := .nat r) (by omega) rfl
  have gr := rcRDW.get a0 (j := 0) (v := natList rowT) rfl
  have gk := rcRDW.get a0 (j := 1) (v := natList keys) rfl
  have gh := rcRDW.get a0 (j := 2) (v := natList hl) rfl
  have n0 := rcRDW.nat (P := P) (W := W)
    (env := [.list [.list [natList rowT, natList keys, natList hl], .nat r]]) 0 (by omega)
  have g := rcRDW.gdN I hgD gr (rcRDW.gdN I hgD gh (rcRDW.gdN I hgD gk a1 n0) n0) n0
  exact (rcRDW.fn hf g).mono (by omega)

end Tests

end GI.Impl
