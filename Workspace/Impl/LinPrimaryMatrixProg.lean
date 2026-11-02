import Workspace.Impl.LinPrimaryMatrixCell
import Workspace.Impl.LinTabulate

/-! Tabulate the retained-coordinate field matrix from a full homogeneous
matrix, the cyclic exponents and the current level. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryMatrixRowF (tab : ℕ) : Expr :=
  .call tab (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
      (.get (arg 0) (.nat 2)) (arg 1)) (.length (.get (arg 0) (.nat 1))))
def linPrimaryMatrixF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.length (arg 1)))

def linPrimaryMatrixFuns (b : ℕ) : List Expr :=
  [linPrimaryMatrixF (b + 3), linPrimaryMatrixRowF (b + 10), linPrimaryMatrixCellF] ++
    linTabulateFuns (b + 3) (b + 1) ++ linTabulateFuns (b + 10) (b + 2)

theorem linPrimaryMatrixFuns_length (b : ℕ) : (linPrimaryMatrixFuns b).length = 17 := rfl

structure linPrimaryMatrixAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryMatrixF (b + 3))
  row : P.funs[b + 1]? = some (linPrimaryMatrixRowF (b + 10))
  cell : P.funs[b + 2]? = some linPrimaryMatrixCellF
  rows : linTabulateAt P (b + 3) (b + 1)
  cols : linTabulateAt P (b + 10) (b + 2)

theorem linPrimaryMatrixAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryMatrixFuns b)) : linPrimaryMatrixAt P b where
  entry := (h.block (gs := [linPrimaryMatrixF (b + 3)]) 0 rfl).single
  row := (h.block (gs := [linPrimaryMatrixRowF (b + 10)]) 1 rfl).single
  cell := (h.block (gs := [linPrimaryMatrixCellF]) 2 rfl).single
  rows := linTabulateAt_of (h.block 3 rfl)
  cols := linTabulateAt_of (h.block 10 rfl)

def linPrimaryMatrixRowCost (W d : ℕ) : ℕ :=
  10000 * (W + d + linTabulateCost (100 * (W + d + 1)) d
    (100000 * (100 * (W + d + 1) + 1)) + 1)
def linPrimaryMatrixCost (W d : ℕ) : ℕ :=
  10000 * (W + d + linTabulateCost (100 * (W + d + 1)) d
    (linPrimaryMatrixRowCost (100 * (W + d + 1)) d) + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linPrimaryMatrixRow_spec {P : Program} {b p d : ℕ} (h : linPrimaryMatrixAt P b)
    (hp : p.Prime) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod p))
    (ν : Fin d → ℕ) (level : ℕ) (i : Fin d) :
    FunDet P (b + 1) (.list [.list [encModMatrix A, encFun ν, .nat level], .nat i])
      (encVec (linActiveMatrix (fun i => level < ν i) (A.submatrix Fin.castSucc Fin.castSucc) i))
      (linPrimaryMatrixRowCost (Val.list [.list [encModMatrix A, encFun ν, .nat level], .nat i]).wt d) := by
  let c := Val.list [encModMatrix A, encFun ν, .nat level]
  let a := Val.list [c, .nat i]
  let W := a.wt
  let ctx := Val.list [encModMatrix A, encFun ν, .nat level, .nat i]
  let M := linActiveMatrix (fun i => level < ν i) (A.submatrix Fin.castSucc Fin.castSucc)
  have wc : c.wt < W := wt_le_wt_list (by simp [W, a])
  have wA : (encModMatrix A).wt < c.wt := wt_le_wt_list (by simp [c])
  have wν : (encFun ν).wt < c.wt := wt_le_wt_list (by simp [c])
  have wl : (Val.nat level).wt < c.wt := wt_le_wt_list (by simp [c])
  have wi := wt_nat_le i.val
  have wd := wt_nat_le d
  have hctx : ctx.wt ≤ 20 * (W + d + 1) := by
    have hh := wt_list4_le (encModMatrix A) (encFun ν) (.nat level) (.nat i)
    have := i.isLt
    dsimp only [ctx]
    omega
  have htab : (Val.list [ctx, .nat d]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le ctx (.nat d)
    omega
  have hcell (k : Fin d) : (Val.list [ctx, .nat k]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le ctx (.nat k)
    have hw := wt_nat_le k.val
    have := k.isLt
    omega
  have ht := linTabulate_spec h.cols ctx (fun k : Fin d => Val.nat (M i k).val)
    (100000 * (100 * (W + d + 1) + 1)) (fun k =>
      (linPrimaryMatrixCell_spec h.cell hp A ν level i k).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hcell k) 1)))
  have ht' := ht.mono (linTabulateCost_mono htab le_rfl le_rfl)
  have dc := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have da := Det.get' dc (Det.nat 0) rfl
  have dν := Det.get' dc (Det.nat 1) rfl
  have dl := Det.get' dc (Det.nat 2) rfl
  have dn := Det.length dν
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 (Det.mk4 da dν dl di) dn) ht'
  apply FunDet.intro h.row
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have wmk := wt_list4_le (encModMatrix A) (encFun ν) (.nat level) (.nat i)
  have wta := wt_list2_le ctx (.nat d)
  change _ ≤ linPrimaryMatrixRowCost W d
  dsimp only [linPrimaryMatrixRowCost]
  dsimp only [ctx, W, a, c, M, encFun, encVec, encModMatrix] at *
  omega

theorem linPrimaryMatrixRowCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linPrimaryMatrixRowCost W d ≤ linPrimaryMatrixRowCost V e := by
  unfold linPrimaryMatrixRowCost linTabulateCost linTabulateRangeCost linMapBudget
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linPrimaryMatrix_spec {P : Program} {b p d : ℕ} (h : linPrimaryMatrixAt P b)
    (hp : p.Prime) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod p))
    (ν : Fin d → ℕ) (level : ℕ) :
    FunDet P b (.list [encModMatrix A, encFun ν, .nat level])
      (encModMatrix (linActiveMatrix (fun i => level < ν i) (A.submatrix Fin.castSucc Fin.castSucc)))
      (linPrimaryMatrixCost (Val.list [encModMatrix A, encFun ν, .nat level]).wt d) := by
  let a := Val.list [encModMatrix A, encFun ν, .nat level]
  let W := a.wt
  let M := linActiveMatrix (fun i => level < ν i) (A.submatrix Fin.castSucc Fin.castSucc)
  have ww : (Val.list [a, .nat d]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat d)
    have hw := wt_nat_le d
    omega
  have wi (i : Fin d) : (Val.list [a, .nat i]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat i)
    have hw := wt_nat_le i.val
    have := i.isLt
    omega
  have ht := linTabulate_spec h.rows a (fun i => encVec (M i))
    (linPrimaryMatrixRowCost (100 * (W + d + 1)) d) (fun i =>
      (linPrimaryMatrixRow_spec h hp A ν level i).mono (linPrimaryMatrixRowCost_mono (wi i) le_rfl))
  have ht' := ht.mono (linTabulateCost_mono ww le_rfl le_rfl)
  have dn := Det.length (Det.arg' (P := P) (vs := [encModMatrix A, encFun ν, .nat level]) (rest := []) (j := 1) rfl)
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl) dn) ht'
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have wd := wt_nat_le d
  have ww' := wt_list2_le a (.nat d)
  change _ ≤ linPrimaryMatrixCost W d
  dsimp only [linPrimaryMatrixCost]
  dsimp only [W, a, M, encFun, encVec, encModMatrix] at *
  omega

theorem linPrimaryMatrixCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linPrimaryMatrixCost W d ≤ linPrimaryMatrixCost V e := by
  simp only [linPrimaryMatrixCost, linPrimaryMatrixRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

theorem linPrimaryMatrixCost_poly : PBU (fun d W _ => linPrimaryMatrixCost W d) := by
  simp only [linPrimaryMatrixCost, linPrimaryMatrixRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
