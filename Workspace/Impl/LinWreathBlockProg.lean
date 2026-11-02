import Workspace.Impl.LinWreathBlock
import Workspace.Impl.LinTabulate

/-! Tabulate the two-copy generator matrices using the cell routine. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linWreathBlockRowF (tab : ℕ) : Expr :=
  .call tab (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.arith .add (.length (.get (arg 0) (.nat 0))) (.length (.get (arg 0) (.nat 0)))))

def linWreathBlockF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0) (.arith .add (.length (arg 0)) (.length (arg 0))))

def linWreathBlockFuns (b : ℕ) : List Expr :=
  [linWreathBlockF (b + 3), linWreathBlockRowF (b + 10), linWreathBlockCellF] ++
    linTabulateFuns (b + 3) (b + 1) ++ linTabulateFuns (b + 10) (b + 2)

theorem linWreathBlockFuns_length (b : ℕ) : (linWreathBlockFuns b).length = 17 := rfl

structure linWreathBlockAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathBlockF (b + 3))
  row : P.funs[b + 1]? = some (linWreathBlockRowF (b + 10))
  cell : P.funs[b + 2]? = some linWreathBlockCellF
  rows : linTabulateAt P (b + 3) (b + 1)
  cols : linTabulateAt P (b + 10) (b + 2)

theorem linWreathBlockAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathBlockFuns b)) : linWreathBlockAt P b where
  entry := (h.block (gs := [linWreathBlockF (b + 3)]) 0 rfl).single
  row := (h.block (gs := [linWreathBlockRowF (b + 10)]) 1 rfl).single
  cell := (h.block (gs := [linWreathBlockCellF]) 2 rfl).single
  rows := linTabulateAt_of (h.block 3 rfl)
  cols := linTabulateAt_of (h.block 10 rfl)

def linWreathBlockRowCost (W d : ℕ) : ℕ :=
  10000 * (W + d + linTabulateCost (100 * (W + d + 1)) (d + d)
    (100000 * (100 * (W + d + 1) + d + 1)) + 1)
def linWreathBlockCost (W d : ℕ) : ℕ :=
  10000 * (W + d + linTabulateCost (100 * (W + d + 1)) (d + d)
    (linWreathBlockRowCost (100 * (W + d + 1)) d) + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linWreathBlockRow_spec {P : Program} {b p d : ℕ} (h : linWreathBlockAt P b)
    (hp : p.Prime) (hd : 0 < d) (A : Matrix (Fin d) (Fin d) (ZMod p))
    (mode : Fin 3) (i : Fin (d + d)) :
    FunDet P (b + 1) (.list [.list [encModMatrix A, .nat mode], .nat i])
      (encVec (linWreathBlock hd A mode i))
      (linWreathBlockRowCost (Val.list [.list [encModMatrix A, .nat mode], .nat i]).wt d) := by
  let c := Val.list [encModMatrix A, .nat mode]
  let a := Val.list [c, .nat i]
  let W := a.wt
  let ctx := Val.list [encModMatrix A, .nat mode, .nat i]
  have wc : c.wt < W := wt_le_wt_list (by simp [W, a])
  have wa : (encModMatrix A).wt < c.wt := wt_le_wt_list (by simp [c])
  have wm : (Val.nat mode).wt < c.wt := wt_le_wt_list (by simp [c])
  have wi := wt_nat_le i.val
  have wd := wt_nat_le (d + d)
  have hctx : ctx.wt ≤ 20 * (W + d + 1) := by
    have hh := wt_list3_le (encModMatrix A) (.nat mode) (.nat i)
    have := i.isLt
    dsimp only [ctx]
    omega
  have htab : (Val.list [ctx, .nat (d + d)]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le ctx (.nat (d + d))
    omega
  have hcell (j : Fin (d + d)) :
      (Val.list [ctx, .nat j]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le ctx (.nat j)
    have hj := wt_nat_le j.val
    have := j.isLt
    omega
  have ht := linTabulate_spec h.cols ctx
    (fun j : Fin (d + d) => Val.nat (linWreathBlock hd A mode i j).val)
    (100000 * (100 * (W + d + 1) + d + 1)) (fun j =>
      (linWreathBlockCell_spec h.cell hp hd A mode i j).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right (hcell j) d) 1)))
  have ht' := ht.mono (linTabulateCost_mono htab le_rfl le_rfl)
  have dc := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have da := Det.get' dc (Det.nat 0) rfl
  have dm := Det.get' dc (Det.nat 1) rfl
  have dn := Det.length da
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 (Det.mk3 da dm di) (Det.arith (op := .add) dn dn)) ht'
  apply FunDet.intro h.row
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have wmk := wt_list3_le (encModMatrix A) (.nat mode) (.nat i)
  have wta := wt_list2_le ctx (.nat (d + d))
  change _ ≤ linWreathBlockRowCost W d
  dsimp only [linWreathBlockRowCost]
  dsimp only [ctx, W, a, c, encModMatrix, encVec] at *
  simp only [GI.Machine.BinOp.eval_add]
  omega

theorem linWreathBlockRowCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linWreathBlockRowCost W d ≤ linWreathBlockRowCost V e := by
  unfold linWreathBlockRowCost linTabulateCost linTabulateRangeCost linMapBudget
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linWreathBlock_spec {P : Program} {b p d : ℕ} (h : linWreathBlockAt P b)
    (hp : p.Prime) (hd : 0 < d) (A : Matrix (Fin d) (Fin d) (ZMod p)) (mode : Fin 3) :
    FunDet P b (.list [encModMatrix A, .nat mode])
      (encModMatrix (linWreathBlock hd A mode))
      (linWreathBlockCost (Val.list [encModMatrix A, .nat mode]).wt d) := by
  let a := Val.list [encModMatrix A, .nat mode]
  let W := a.wt
  have ww : (Val.list [a, .nat (d + d)]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat (d + d))
    have hw := wt_nat_le (d + d)
    omega
  have wi (i : Fin (d + d)) : (Val.list [a, .nat i]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat i)
    have hw := wt_nat_le i.val
    have := i.isLt
    omega
  have ht := linTabulate_spec h.rows a (fun i => encVec (linWreathBlock hd A mode i))
    (linWreathBlockRowCost (100 * (W + d + 1)) d) (fun i =>
      (linWreathBlockRow_spec h hp hd A mode i).mono (linWreathBlockRowCost_mono (wi i) le_rfl))
  have ht' := ht.mono (linTabulateCost_mono ww le_rfl le_rfl)
  have da := Det.arg' (P := P) (vs := [encModMatrix A, .nat mode]) (rest := []) (j := 0) rfl
  have dn := Det.length da
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    (Det.arith (op := .add) dn dn)) ht'
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have wa : (encModMatrix A).wt < W := wt_le_wt_list (by simp [W, a])
  have wd := wt_nat_le (d + d)
  have ww' := wt_list2_le a (.nat (d + d))
  change _ ≤ linWreathBlockCost W d
  dsimp only [linWreathBlockCost]
  dsimp only [W, a, encModMatrix, encVec] at *
  simp only [GI.Machine.BinOp.eval_add]
  omega

theorem linWreathBlockCost_poly : PBU (fun d W _ => linWreathBlockCost W d) := by
  unfold linWreathBlockCost linWreathBlockRowCost linTabulateCost linTabulateRangeCost linMapBudget
  norm_poly

end GI.Impl
