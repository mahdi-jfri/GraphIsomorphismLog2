module

public import Workspace.Impl.LinTabulate

@[expose] public section

/-! Build a dense table from a proved scalar program. Explicit row and
column lists in the input pay for the dimensions, including empty tables. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linMatrixTableF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.length (arg 0)))
def linMatrixTableRowF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0) (.length (.get (arg 0) (.nat 1))))

def linMatrixTableFuns (b cell : ℕ) : List Expr :=
  [linMatrixTableF (b + 2), linMatrixTableRowF (b + 9)] ++
    linTabulateFuns (b + 2) (b + 1) ++ linTabulateFuns (b + 9) cell

theorem linMatrixTableFuns_length (b cell : ℕ) : (linMatrixTableFuns b cell).length = 16 := rfl

structure linMatrixTableAt (P : Program) (b cell : ℕ) : Prop where
  entry : P.funs[b]? = some (linMatrixTableF (b + 2))
  row : P.funs[b + 1]? = some (linMatrixTableRowF (b + 9))
  rows : linTabulateAt P (b + 2) (b + 1)
  cols : linTabulateAt P (b + 9) cell

theorem linMatrixTableAt_of {P : Program} {b cell : ℕ}
    (h : P.HasAt b (linMatrixTableFuns b cell)) : linMatrixTableAt P b cell where
  entry := (h.block (gs := [linMatrixTableF (b + 2)]) 0 rfl).single
  row := (h.block (gs := [linMatrixTableRowF (b + 9)]) 1 rfl).single
  rows := linTabulateAt_of (h.block 2 rfl)
  cols := linTabulateAt_of (h.block 9 rfl)

def linMatrixTableArg (W r c : ℕ) : ℕ := 100 * (W + r + c + 1)
def linMatrixTableRowCost (W r c B : ℕ) : ℕ :=
  10000 * (W + r + c + linTabulateCost (linMatrixTableArg W r c) c B + 1)
def linMatrixTableCost (W r c B : ℕ) : ℕ :=
  10000 * (W + r + c + linTabulateCost (linMatrixTableArg W r c) r
    (linMatrixTableRowCost W r c B) + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linMatrixTableRow_spec {P : Program} {b cell B : ℕ}
    (h : linMatrixTableAt P b cell) (rs cs : List Val) (payload : Val)
    (F : Fin rs.length → Fin cs.length → Val) (i : Fin rs.length)
    (hc : ∀ j : Fin cs.length, FunDet P cell
      (.list [.list [.list [.list rs, .list cs, payload], .nat i], .nat j]) (F i j) B) :
    let a := Val.list [.list rs, .list cs, payload]
    FunDet P (b + 1) (.list [a, .nat i]) (.list ((List.finRange cs.length).map (F i)))
      (linMatrixTableRowCost a.wt rs.length cs.length B) := by
  let a := Val.list [.list rs, .list cs, payload]
  let row := Val.list [a, .nat i]
  let W := a.wt
  have wcs : (Val.list cs).wt < W := wt_le_wt_list (by simp [a, W])
  have harg : (Val.list [row, .nat cs.length]).wt ≤ linMatrixTableArg W rs.length cs.length := by
    have hrow := wt_list2_le a (.nat i)
    have hh := wt_list2_le row (.nat cs.length)
    have hi := wt_nat_le i.val
    have hn := wt_nat_le cs.length
    have := i.isLt
    unfold linMatrixTableArg
    dsimp only [row, W] at *
    omega
  have ht := (linTabulate_spec h.cols row (F i) B hc).mono
    (linTabulateCost_mono harg le_rfl le_rfl)
  have da := Det.arg' (P := P) (vs := [a, .nat i]) (rest := []) (j := 0) rfl
  have dcs := Det.get' da (Det.nat 1) rfl
  have dn := Det.length dcs
  have dr := Det.var' (P := P) (env := [row]) (i := 0) rfl
  have dout := Det.call (Det.mk2 dr dn) ht
  apply FunDet.intro h.row
  refine dout.mono ?_
  have wo := ht.wt_lt.le
  have hwrow := wt_list2_le a (.nat i)
  have hwarg := wt_list2_le row (.nat cs.length)
  have hi := wt_nat_le i.val
  have hn := wt_nat_le cs.length
  have := i.isLt
  change _ ≤ linMatrixTableRowCost W rs.length cs.length B
  unfold linMatrixTableRowCost
  dsimp only [row, W, a] at *
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linMatrixTable_spec {P : Program} {b cell B : ℕ}
    (h : linMatrixTableAt P b cell) (rs cs : List Val) (payload : Val)
    (F : Fin rs.length → Fin cs.length → Val)
    (hc : ∀ (i : Fin rs.length) (j : Fin cs.length), FunDet P cell
      (.list [.list [.list [.list rs, .list cs, payload], .nat i], .nat j]) (F i j) B) :
    let a := Val.list [.list rs, .list cs, payload]
    FunDet P b a (.list ((List.finRange rs.length).map fun i =>
      .list ((List.finRange cs.length).map (F i))))
      (linMatrixTableCost a.wt rs.length cs.length B) := by
  let a := Val.list [.list rs, .list cs, payload]
  let W := a.wt
  have wrs : (Val.list rs).wt < W := wt_le_wt_list (by simp [a, W])
  have harg : (Val.list [a, .nat rs.length]).wt ≤ linMatrixTableArg W rs.length cs.length := by
    have hh := wt_list2_le a (.nat rs.length)
    have hn := wt_nat_le rs.length
    unfold linMatrixTableArg
    dsimp only [W] at *
    omega
  have ht := (linTabulate_spec h.rows a
    (fun i : Fin rs.length => Val.list ((List.finRange cs.length).map (F i)))
    (linMatrixTableRowCost W rs.length cs.length B) (fun i =>
      linMatrixTableRow_spec h rs cs payload F i (hc i))).mono
    (linTabulateCost_mono harg le_rfl le_rfl)
  have dn := Det.length (Det.arg' (P := P) (vs := [.list rs, .list cs, payload])
    (rest := []) (j := 0) rfl)
  have da := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dout := Det.call (Det.mk2 da dn) ht
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := ht.wt_lt.le
  have hn := wt_nat_le rs.length
  have hwarg := wt_list2_le a (.nat rs.length)
  change _ ≤ linMatrixTableCost W rs.length cs.length B
  unfold linMatrixTableCost
  dsimp only [W, a] at *
  omega

theorem linMatrixTableCost_mono {W V r s c d B E : ℕ}
    (hW : W ≤ V) (hr : r ≤ s) (hc : c ≤ d) (hB : B ≤ E) :
    linMatrixTableCost W r c B ≤ linMatrixTableCost V s d E := by
  simp only [linMatrixTableCost, linMatrixTableRowCost, linMatrixTableArg,
    linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

theorem linMatrixTable_spec_length {P : Program} {b cell B r c : ℕ}
    (h : linMatrixTableAt P b cell) (rs cs : List Val) (payload : Val)
    (hr : rs.length = r) (hc : cs.length = c) (F : Fin r → Fin c → Val)
    (hf : ∀ (i : Fin r) (j : Fin c), FunDet P cell
      (.list [.list [.list [.list rs, .list cs, payload], .nat i], .nat j]) (F i j) B) :
    FunDet P b (.list [.list rs, .list cs, payload])
      (.list ((List.finRange r).map fun i => .list ((List.finRange c).map (F i))))
      (linMatrixTableCost (Val.list [.list rs, .list cs, payload]).wt r c B) := by
  subst r
  subst c
  exact linMatrixTable_spec h rs cs payload F hf

end GI.Impl
