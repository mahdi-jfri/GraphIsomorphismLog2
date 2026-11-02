import Workspace.Impl.AggItemCiCfgP

/-!
# The configuration query: the pair colors as a program

`itcqFV X` is the list of the fiber points (`natList`). `itcqPcF` computes the pair color of
position `t`: on `[[rcColVal X, itcqFV X, n], t]` it reads the fiber points `a = F[t / n]`,
`b = F[t % n]` and returns `col a b` (`itcq_pcF_spec`). That is `itcqPC X rfl` at
`(itciPE n).symm t` (`itcq_pc_eq`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)

variable {q : ℕ}

/-- The fiber points, as a list of numbers. -/
def itcqFV (X : PairCfg q) : Val := natList ((itciFl X.fiber).map Fin.val)

/-- On `[[col table, fiber points, n], t]`: the pair color of position `t`. -/
def itcqPcF : Expr :=
  .letE (.get (.get (arg 0) (.nat 1)) (.arith .div (arg 1) (.get (arg 0) (.nat 2))))
    (.letE (.get (.get (arg 0) (.nat 1)) (.arith .mod (arg 1) (.get (arg 0) (.nat 2))))
      (.get (.get (.get (arg 0) (.nat 0)) (.var 1)) (.var 2)))

theorem itcq_pc_eq (X : PairCfg q) (t : Fin (X.fiber.card * X.fiber.card)) :
    itcqPC X rfl ((itciPE _).symm t) =
      X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by
          rw [itciFl_length]; exact ((itciPE _).symm t).1.isLt))
        ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by
          rw [itciFl_length]; exact ((itciPE _).symm t).2.isLt)) := by
  unfold itcqPC
  rw [itci_emb_eq, itci_emb_eq]
  rfl

theorem itcq_fv_get (X : PairCfg q) {i : ℕ} (hi : i < X.fiber.card) :
    ((itciFl X.fiber).map Fin.val |>.map Val.nat)[i]? =
      some (.nat ((itciFl X.fiber)[i]'(by rw [itciFl_length]; exact hi) : ℕ)) := by
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem]
  rfl

theorem itcq_col_get (X : PairCfg q) (a : Fin q) :
    ((List.finRange q).map fun a => encFun (X.col a))[(a : ℕ)]? = some (encFun (X.col a)) := by
  simp

section Prog

variable {P : Program}

/-- **The pair color of a position**, in cost `50 (W + 1)`. -/
theorem itcq_pcF_spec {f : ℕ} (hf : P.funs[f]? = some itcqPcF) (X : PairCfg q)
    (t : Fin (X.fiber.card * X.fiber.card)) {W : ℕ}
    (hW : (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt ≤ W) :
    FunDet P f (.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t])
      (.nat (itcqPC X rfl ((itciPE _).symm t))) (50 * (W + 1)) := by
  have hd : (t : ℕ) / X.fiber.card < X.fiber.card := ((itciPE X.fiber.card).symm t).1.isLt
  have hm : (t : ℕ) % X.fiber.card < X.fiber.card := ((itciPE X.fiber.card).symm t).2.isLt
  have hl0 : (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt ≤ (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt := st_wt_mem (by simp)
  have hc : (rcColVal X).wt ≤ (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt := st_wt_mem (by simp)
  have hF : (itcqFV X).wt ≤ (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt := st_wt_mem (by simp)
  have hN : (Val.nat X.fiber.card).wt ≤ (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt := st_wt_mem (by simp)
  have hT : (Val.nat t).wt ≤ (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt := st_wt_mem (by simp)
  have haw : (Val.nat (((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)) : ℕ)).wt ≤ (itcqFV X).wt :=
    st_wt_mem (List.mem_of_getElem? (itcq_fv_get X hd))
  have hbw : (Val.nat (((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm)) : ℕ)).wt ≤ (itcqFV X).wt :=
    st_wt_mem (List.mem_of_getElem? (itcq_fv_get X hm))
  have hrw : (encFun (X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)))).wt ≤ (rcColVal X).wt :=
    st_wt_mem (List.mem_of_getElem? (itcq_col_get X ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))))
  have hvw : (Val.nat (X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)) ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm)))).wt ≤ (encFun (X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)))).wt :=
    st_wt_mem (List.mem_of_getElem? (encFun_getElem? (X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))) ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))))
  have hdw : (Val.nat ((t : ℕ) / X.fiber.card)).wt ≤ (Val.nat t).wt := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono (Nat.div_le_self (t : ℕ) X.fiber.card); omega
  have hmw : (Val.nat ((t : ℕ) % X.fiber.card)).wt ≤ (Val.nat t).wt := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono (Nat.mod_le (t : ℕ) X.fiber.card); omega
  have h2 := wt_nat_le 2
  have hAW : (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt ≤ W := hW
  have hA4 : 4 ≤ (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt := by
    have h1 : (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt < (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt :=
      wt_le_wt_list (by simp)
    have h2 : (Val.nat X.fiber.card).wt < (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt :=
      wt_le_wt_list (by simp)
    have := wt_nat X.fiber.card
    omega
  have A0 : ∀ rest : List Val, StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: rest) (arg 0)
      (.list [rcColVal X, itcqFV X, .nat X.fiber.card]) 3 0 W := fun rest =>
    StDC.arg (vs := [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) rfl (by omega) (by omega)
      (by omega)
  have A1 : ∀ rest : List Val, StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: rest) (arg 1) (.nat t) 3 0 W := fun rest =>
    StDC.arg (vs := [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) rfl (by omega) (by omega)
      (by omega)
  have GF : ∀ rest : List Val, StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: rest) (.get (arg 0) (.nat 1)) (itcqFV X) 5 0 W :=
    fun rest => (StDC.get (A0 rest) (StDC.nat 1 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have GN : ∀ rest : List Val, StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: rest) (.get (arg 0) (.nat 2)) (.nat X.fiber.card) 5 0 W :=
    fun rest => (StDC.get (A0 rest) (StDC.nat 2 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have GC : ∀ rest : List Val, StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: rest) (.get (arg 0) (.nat 0)) (rcColVal X) 5 0 W :=
    fun rest => (StDC.get (A0 rest) (StDC.nat 0 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have dv := StDC.arith (A1 []) (GN []) (op := .div) (z := (t : ℕ) / X.fiber.card) rfl (by omega)
  have ga := StDC.get (GF []) dv (itcq_fv_get X hd) (by omega)
  have md := StDC.arith (A1 [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))]) (GN [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))]) (op := .mod) (z := (t : ℕ) % X.fiber.card) rfl
    (by omega)
  have gb := StDC.get (GF [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))]) md (itcq_fv_get X hm) (by omega)
  have v1 : StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)), .nat ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))]) (.var 1) (.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))) 1 0 W := StDC.var' rfl (by omega)
  have v2 : StDC P ((Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]) :: [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)), .nat ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))]) (.var 2) (.nat ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))) 1 0 W := StDC.var' rfl (by omega)
  have r1 := StDC.get (GC [.nat ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd)), .nat ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))]) v1 (itcq_col_get X ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))) (by omega)
  have r2 := StDC.get r1 v2 (encFun_getElem? (X.col ((itciFl X.fiber)[(t : ℕ) / X.fiber.card]'(by rw [itciFl_length]; exact hd))) ((itciFl X.fiber)[(t : ℕ) % X.fiber.card]'(by rw [itciFl_length]; exact hm))) (by omega)
  have l2 := StDC.letE gb r2 (by omega)
  have l1 := StDC.letE ga l2 (by omega)
  rw [itcq_pc_eq]
  exact StDC.funDet hf l1 (by omega)

/-- On `[rcCertIn X x₀, a]`: whether `a` is in the fiber (`col a a = j`). -/
def itcqFbT : Expr :=
  .arith .eq (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (arg 1)) (.get (arg 0) (.nat 1))

/-- The fiber test on values. -/
def itcqFq (X : PairCfg q) : Val → Bool
  | .nat a => if h : a < q then decide (X.col ⟨a, h⟩ ⟨a, h⟩ = X.j) else false
  | _ => false

theorem itcq_fq_filter (X : PairCfg q) :
    ((List.range q).map Val.nat).filter (itcqFq X) = ((itciFl X.fiber).map Fin.val).map Val.nat := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.filter_map, itciFl, List.map_map]
  congr 2
  funext a
  simp [itcqFq, PairCfg.mem_fiber, a.isLt]

/-- **The fiber test**, in cost `30 (W + 1)`. -/
theorem itcq_fbT_spec {f : ℕ} (hf : P.funs[f]? = some itcqFbT) (X : PairCfg q) (x₀ : ℕ)
    (a : Fin q) {W : ℕ} (hW : (Val.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]).wt ≤ W) :
    FunDet P f (.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a])
      (boolVal (itcqFq X (.nat a))) (30 * (W + 1)) := by
  have hl0 : (Val.list [rcColVal X, .nat X.j, .nat x₀]).wt <
      (Val.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]).wt := wt_le_wt_list (by simp)
  have hc : (rcColVal X).wt ≤ (Val.list [rcColVal X, .nat X.j, .nat x₀]).wt := st_wt_mem (by simp)
  have hj : (Val.nat X.j).wt < (Val.list [rcColVal X, .nat X.j, .nat x₀]).wt :=
    wt_le_wt_list (by simp)
  have ha : (Val.nat a).wt ≤ (Val.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]).wt :=
    st_wt_mem (by simp)
  have hrw : (encFun (X.col a)).wt ≤ (rcColVal X).wt :=
    st_wt_mem (List.mem_of_getElem? (itcq_col_get X a))
  have hvw : (Val.nat (X.col a a)).wt ≤ (encFun (X.col a)).wt :=
    st_wt_mem (List.mem_of_getElem? (encFun_getElem? (X.col a) a))
  have h2 := wt_nat_le 2
  have hjw := wt_nat X.j
  have A0 : StDC P [.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]] (arg 0)
      (.list [rcColVal X, .nat X.j, .nat x₀]) 3 0 W :=
    StDC.arg (vs := [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]) rfl (by omega) (by omega)
      (by omega)
  have A1 : StDC P [.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]] (arg 1) (.nat a) 3 0 W :=
    StDC.arg (vs := [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]) rfl (by omega) (by omega)
      (by omega)
  have g0 := StDC.get A0 (StDC.nat 0 (by omega)) (v := rcColVal X) rfl (by omega)
  have g1 := StDC.get A0 (StDC.nat 1 (by omega)) (v := .nat X.j) rfl (by omega)
  have r1 := StDC.get g0 A1 (itcq_col_get X a) (by omega)
  have r2 := StDC.get r1 A1 (encFun_getElem? (X.col a) a) (by omega)
  have hb : Machine.BinOp.eq.eval (X.col a a) X.j = (itcqFq X (.nat a)).toNat := by
    simp only [Machine.BinOp.eval_eq, itcqFq, dif_pos a.isLt, Fin.eta]
    split_ifs <;> simp_all
  have e := StDC.arith r2 g1 hb ((wt_boolVal_le _).trans (by omega))
  exact StDC.funDet hf e (by omega)

end Prog

end GI.Impl
