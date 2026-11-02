import Workspace.Impl.LinMatrixTable
import Workspace.Impl.LinObjectBlockPresentation
import Workspace.Lang.Lib.LinIntTests
import Workspace.Lang.Lib.LinIntVector

/-! The diagonal relation rows, assembled without enumerating elements
of `A/N`. One original coordinate is repeated in every local block. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectDiagonalInput (p d : ℕ) : Val :=
  .list [encFun (fun i : Fin d => i.val), encFun (fun i : Fin (d * p) => i.val), .nat p]

def linObjectDiagonalCellF : Expr :=
  .ite (.arith .eq (.get (arg 0) (.nat 1))
    (.arith .div (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 2)))) linIntOneE linIntZeroE

def linObjectDiagonalFuns (b : ℕ) : List Expr :=
  linMatrixTableFuns b (b + 16) ++ [linObjectDiagonalCellF]

theorem linObjectDiagonalFuns_length (b : ℕ) : (linObjectDiagonalFuns b).length = 17 := rfl

structure linObjectDiagonalAt (P : Program) (b : ℕ) : Prop where
  table : linMatrixTableAt P b (b + 16)
  cell : P.funs[b + 16]? = some linObjectDiagonalCellF

theorem linObjectDiagonalAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linObjectDiagonalFuns b)) : linObjectDiagonalAt P b where
  table := linMatrixTableAt_of h.left
  cell := by simpa only [linMatrixTableFuns_length] using h.right.single

set_option maxHeartbeats 150000 in
set_option maxRecDepth 5000 in
theorem linObjectDiagonalCell_spec {P : Program} {f p d : ℕ}
    (hf : P.funs[f]? = some linObjectDiagonalCellF) (i : Fin d) (k : Fin (d * p)) :
    let a := Val.list [.list [linObjectDiagonalInput p d, .nat i], .nat k]
    FunDet P f a (encInt (linObjectDiagonalMatrix p d i k)) (100000 * (a.wt + 1)) := by
  let input := linObjectDiagonalInput p d
  let ctx := Val.list [input, .nat i]
  let a := Val.list [ctx, .nat k]
  let W := a.wt
  let q : Fin d := (finProdFinEquiv.symm k).1
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wk : (Val.nat k).wt < W := wt_le_wt_list (by simp [a, W])
  have win : input.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wi : (Val.nat i).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wp : (Val.nat p).wt < input.wt := wt_le_wt_list (by simp [input, linObjectDiagonalInput])
  have wd : (encFun (fun i : Fin d => i.val)).wt < input.wt :=
    wt_le_wt_list (by simp [input, linObjectDiagonalInput])
  have hd : d < W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i : Fin d => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun (fun i : Fin d => i.val)).wt at hh
    omega
  have wq : (Val.nat q).wt ≤ W + 2 := by
    have hh := wt_nat_le q.val
    have := q.isLt
    omega
  have dc := Det.arg' (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 0) rfl
  have dk := Det.arg' (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 1) rfl
  have di := Det.get' dc (Det.nat 1) rfl
  have din := Det.get' dc (Det.nat 0) rfl
  have dp := Det.get' din (Det.nat 2) rfl
  have ddiv := Det.arith' (op := .div) dk dp (z := q.val) rfl
  have deq := Det.arith (op := .eq) di ddiv
  have dz : Det P [a] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have done : Det P [a] linIntOneE (encInt 1) 100 :=
    (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))).mono (by decide)
  have dr := Det.ite' deq done dz
  have he : (if GI.Machine.BinOp.eq.eval i.val q.val = 0 then encInt 0 else encInt 1) =
      encInt (linObjectDiagonalMatrix p d i k) := by
    change (if GI.Machine.BinOp.eq.eval i.val q.val = 0 then encInt 0 else encInt 1) =
      encInt (if i = q then 1 else 0)
    by_cases hi : i = q
    · simp [GI.Machine.BinOp.eval, hi]
    · have hv : i.val ≠ q.val := fun h => hi (Fin.ext h)
      simp [GI.Machine.BinOp.eval, hi, hv]
  rw [he] at dr
  have hw0 : (encInt 0).wt = 15 := by decide
  have hw1 : (encInt 1).wt = 21 := by decide
  have wout : (encInt (linObjectDiagonalMatrix p d i k)).wt ≤ 21 := by
    unfold linObjectDiagonalMatrix
    split_ifs <;> omega
  have wbool : (Val.nat (GI.Machine.BinOp.eq.eval i.val q.val)).wt ≤ 3 := by
    simp only [GI.Machine.BinOp.eval]
    split_ifs <;> decide
  apply FunDet.intro hf
  have hqn := q.isLt
  exact dr.mono (by dsimp only [a, W, ctx, input] at *; omega)

def linObjectDiagonalCost (W : ℕ) : ℕ :=
  linMatrixTableCost W W W (100000 * (1000 * (W + 1) + 1))

set_option maxHeartbeats 150000 in
set_option maxRecDepth 5000 in
theorem linObjectDiagonal_spec {P : Program} {b p d : ℕ}
    (h : linObjectDiagonalAt P b) :
    FunDet P b (linObjectDiagonalInput p d) (encIntMatrix (linObjectDiagonalMatrix p d))
      (linObjectDiagonalCost (linObjectDiagonalInput p d).wt) := by
  let a := linObjectDiagonalInput p d
  let W := a.wt
  have wr : (encFun (fun i : Fin d => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectDiagonalInput])
  have wc : (encFun (fun i : Fin (d * p) => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectDiagonalInput])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i : Fin d => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun (fun i : Fin d => i.val)).wt at hh
    omega
  have hdp : d * p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (d * p)).map fun i : Fin (d * p) => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change d * p < (encFun (fun i : Fin (d * p) => i.val)).wt at hh
    omega
  have harg (i : Fin d) (k : Fin (d * p)) :
      (Val.list [.list [a, .nat i], .nat k]).wt ≤ 1000 * (W + 1) := by
    have hw1 := wt_list2_le a (.nat i)
    have hw2 := wt_list2_le (.list [a, .nat i]) (.nat k)
    have hi := wt_nat_le i.val
    have hk := wt_nat_le k.val
    have hid := i.isLt
    have hkc := k.isLt
    dsimp only [W] at *
    omega
  have ht := linMatrixTable_spec_length (B := 100000 * (1000 * (W + 1) + 1)) h.table
    ((List.finRange d).map fun i : Fin d => Val.nat i.val)
    ((List.finRange (d * p)).map fun i : Fin (d * p) => Val.nat i.val) (.nat p)
    (r := d) (c := d * p) (by simp) (by simp)
    (fun i k => encInt (linObjectDiagonalMatrix p d i k))
    (fun i k =>
      (linObjectDiagonalCell_spec h.cell i k).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (harg i k) 1)))
  exact ht.mono (linMatrixTableCost_mono le_rfl hd hdp le_rfl)

theorem linObjectDiagonalCost_poly : PBU (fun _ W _ => linObjectDiagonalCost W) := by
  simp only [linObjectDiagonalCost, linMatrixTableCost, linMatrixTableRowCost,
    linMatrixTableArg, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
