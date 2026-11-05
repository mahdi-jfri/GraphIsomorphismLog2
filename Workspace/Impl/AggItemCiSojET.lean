module

public import Workspace.Impl.AggItemCiSojEdge
public import Workspace.Impl.AggItemCiCfgS

@[expose] public section

/-!
# Testing one undirected color edge from its table

The test includes both fiber memberships. This gives no edges at omitted labels,
so their component labels remain singleton labels.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[table, j, v, a, b]`, test an undirected edge of color `v` in the fiber. -/
def itcsEdgeT : Expr :=
  let caa := Expr.get (.get (arg 0) (arg 3)) (arg 3)
  let cbb := Expr.get (.get (arg 0) (arg 4)) (arg 4)
  let cab := Expr.get (.get (arg 0) (arg 3)) (arg 4)
  let cba := Expr.get (.get (arg 0) (arg 4)) (arg 3)
  .arith .mul (.arith .eq caa (arg 1))
    (.arith .mul (.arith .eq cbb (arg 1))
      (.arith .lt (.nat 0) (.arith .add (.arith .eq cab (arg 2)) (.arith .eq cba (arg 2)))))

open Classical in
/-- Arithmetic form of the edge predicate. -/
theorem itcs_edge_arith (X : PairCfg q) (v : ℕ) (a b : Fin q) :
    (if X.col a a = X.j then 1 else 0) *
      ((if X.col b b = X.j then 1 else 0) *
        (if 0 < (if X.col a b = v then 1 else 0) + (if X.col b a = v then 1 else 0)
          then 1 else 0)) = (decide (X.edge v a b)).toNat := by
  classical
  simp only [PairCfg.edge, PairCfg.mem_fiber]
  by_cases h1 : X.col a a = X.j <;> by_cases h2 : X.col b b = X.j <;>
    by_cases h3 : X.col a b = v <;> by_cases h4 : X.col b a = v <;> simp [h1, h2, h3, h4]

open Classical in
/-- The edge test is a fixed table-reading program. -/
theorem itcs_edgeT_spec {Pg : Program} {f : ℕ} (hf : Pg.funs[f]? = some itcsEdgeT)
    (X : PairCfg q) (v : ℕ) (a b : Fin q) {W : ℕ}
    (hW : (Val.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b]).wt ≤ W) (h8 : 8 ≤ W) :
    FunDet Pg f (.list [rcColVal X, .nat X.j, .nat v, .nat a, .nat b])
      (boolVal (decide (X.edge v a b))) (100 * (W + 1)) := by
  classical
  let vs : List Val := [rcColVal X, .nat X.j, .nat v, .nat a, .nat b]
  let env : List Val := [.list vs]
  have hv : ∀ {i : ℕ} {w : Val}, vs[i]? = some w → w.wt ≤ W := by
    intro i w hi
    exact (st_wt_mem (List.mem_of_getElem? hi)).trans hW
  have g0 : StDC Pg env (arg 0) (rcColVal X) 3 0 W :=
    StDC.arg rfl hW (by omega) (hv (i := 0) rfl)
  have gj : StDC Pg env (arg 1) (.nat X.j) 3 0 W :=
    StDC.arg rfl hW (by omega) (hv (i := 1) rfl)
  have gv : StDC Pg env (arg 2) (.nat v) 3 0 W :=
    StDC.arg rfl hW (by omega) (hv (i := 2) rfl)
  have ga : StDC Pg env (arg 3) (.nat a) 3 0 W :=
    StDC.arg rfl hW (by omega) (hv (i := 3) rfl)
  have gb : StDC Pg env (arg 4) (.nat b) 3 0 W :=
    StDC.arg rfl hW (by omega) (hv (i := 4) rfl)
  have row (x : Fin q) : (encFun (X.col x)).wt ≤ W :=
    (st_wt_mem (List.mem_of_getElem? (itcq_col_get X x))).trans (hv (i := 0) rfl)
  have cell (x y : Fin q) : (Val.nat (X.col x y)).wt ≤ W :=
    (st_wt_mem (List.mem_of_getElem? (encFun_getElem? (X.col x) y))).trans (row x)
  have ra := StDC.get g0 ga (itcq_col_get X a) (row a)
  have rb := StDC.get g0 gb (itcq_col_get X b) (row b)
  have caa := StDC.get ra ga (encFun_getElem? (X.col a) a) (cell a a)
  have cbb := StDC.get rb gb (encFun_getElem? (X.col b) b) (cell b b)
  have cab := StDC.get ra gb (encFun_getElem? (X.col a) b) (cell a b)
  have cba := StDC.get rb ga (encFun_getElem? (X.col b) a) (cell b a)
  have ej := StDC.arith' caa gj (op := .eq) (z := if X.col a a = X.j then 1 else 0)
    (by simp [Machine.BinOp.eval_eq]) (by split_ifs <;> omega)
  have ek := StDC.arith' cbb gj (op := .eq) (z := if X.col b b = X.j then 1 else 0)
    (by simp [Machine.BinOp.eval_eq]) (by split_ifs <;> omega)
  have eab := StDC.arith' cab gv (op := .eq) (z := if X.col a b = v then 1 else 0)
    (by simp [Machine.BinOp.eval_eq]) (by split_ifs <;> omega)
  have eba := StDC.arith' cba gv (op := .eq) (z := if X.col b a = v then 1 else 0)
    (by simp [Machine.BinOp.eval_eq]) (by split_ifs <;> omega)
  have es := StDC.arith' eab eba (op := .add)
    (z := (if X.col a b = v then 1 else 0) + (if X.col b a = v then 1 else 0))
    rfl (by split_ifs <;> omega)
  have ep := StDC.arith' (StDC.nat 0 (by omega)) es (op := .lt)
    (z := if 0 < (if X.col a b = v then 1 else 0) + (if X.col b a = v then 1 else 0)
      then 1 else 0) (by simp [Machine.BinOp.eval_lt]) (by split_ifs <;> omega)
  have em := StDC.arith' ek ep (op := .mul) rfl (by split_ifs <;> norm_num <;> omega)
  have ee := StDC.arith' ej em (op := .mul) rfl (by split_ifs <;> norm_num <;> omega)
  simp only [Machine.BinOp.eval_mul] at ee
  rw [itcs_edge_arith] at ee
  exact StDC.funDet hf ee (by omega)

end GI.Impl
