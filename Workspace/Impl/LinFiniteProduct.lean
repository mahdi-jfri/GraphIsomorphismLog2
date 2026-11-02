import Workspace.Impl.LinDenseMul
import Workspace.Impl.LinFiniteHomogeneous

/-! Multiply full affine matrices and reduce every target-coordinate row. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linFiniteProductF (mul red : ℕ) : Expr :=
  .letE (.call mul (mk2 (mk2 (.length (arg 0)) (arg 2)) (arg 1)))
    (.call red (mk2 (arg 0) (.var 1)))

def linFiniteProductFuns (b : ℕ) : List Expr :=
  [linFiniteProductF (b + 1) (b + 33)] ++ linDenseMulFuns (b + 1) ++ linFiniteMatrixReduceFuns (b + 33)

theorem linFiniteProductFuns_length (b : ℕ) : (linFiniteProductFuns b).length = 58 := rfl

structure linFiniteProductAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linFiniteProductF (b + 1) (b + 33))
  mul : linDenseMulAt P (b + 1)
  red : P.HasAt (b + 33) (linFiniteMatrixReduceFuns (b + 33))

theorem linFiniteProductAt_of {P : Program} {b : ℕ} (h : P.HasAt b (linFiniteProductFuns b)) :
    linFiniteProductAt P b where
  entry := (h.block (gs := [linFiniteProductF (b + 1) (b + 33)]) 0 rfl).single
  mul := linDenseMulAt_of (h.block 1 rfl)
  red := h.block 33 rfl

def linFiniteProductMulBudget (W n : ℕ) : ℕ := linMatrixMulCost (100 * (W + 1)) n n n
def linFiniteProductReduceBudget (W n : ℕ) : ℕ :=
  linFiniteMatrixReduceCost (10 * (W + linFiniteProductMulBudget W n + 1)) n
def linFiniteProductCost (W n : ℕ) : ℕ :=
  10000 * (W + n + linFiniteProductMulBudget W n + linFiniteProductReduceBudget W n + 1)

theorem linFiniteMatrixReduceCost_mono {W V r : ℕ} (hW : W ≤ V) :
    linFiniteMatrixReduceCost W r ≤ linFiniteMatrixReduceCost V r := by
  unfold linFiniteMatrixReduceCost linFiniteMatrixReduceStepCost linFiniteMatrixReduceAcc
    linFiniteMatrixReduceRowBudget linConstRemCost linMapBudget linScalarRemCost
    linVectorAccWt linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linFiniteProduct_spec {P : Program} {b n : ℕ} (hp : linFiniteProductAt P b)
    (m : Fin n → ℤ) (A B : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P b (.list [linVecVal m, encIntMatrix A, encIntMatrix B])
      (encIntMatrix (fun i j => (A * B) i j % m i))
      (linFiniteProductCost (Val.list [linVecVal m, encIntMatrix A, encIntMatrix B]).wt n) := by
  let a := Val.list [linVecVal m, encIntMatrix A, encIntMatrix B]
  let W := a.wt
  let MC := linFiniteProductMulBudget W n
  let RC := linFiniteProductReduceBudget W n
  have wm : (linVecVal m).wt < W := wt_le_wt_list (by simp [W, a])
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [W, a])
  have wB : (encIntMatrix B).wt < W := wt_le_wt_list (by simp [W, a])
  have wn := wt_nat_le n
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => encInt (m i))
    simp only [List.length_map, List.length_finRange] at hh
    exact hh.le.trans wm.le
  have wc := wt_list2_le (.nat n) (encIntMatrix B)
  have wi := wt_list2_le (.list [.nat n, encIntMatrix B]) (encIntMatrix A)
  have ww : (Val.list [.list [.nat n, encIntMatrix B], encIntMatrix A]).wt ≤ 100 * (W + 1) := by omega
  have hs := (linDenseMul_spec hp.mul A B).mono (linDenseMulCost_mono ww)
  have ws : (encIntMatrix (A * B)).wt ≤ MC := hs.wt_lt.le
  have wr := wt_list2_le (linVecVal m) (encIntMatrix (A * B))
  have ww' : (Val.list [linVecVal m, encIntMatrix (A * B)]).wt ≤ 10 * (W + MC + 1) := by omega
  have hr := (linFiniteMatrixReduce_spec hp.red m (A * B)).mono (linFiniteMatrixReduceCost_mono ww')
  have wo : (encIntMatrix (fun i j => (A * B) i j % m i)).wt ≤ RC := hr.wt_lt.le
  have da (i : ℕ) (rest : List Val) {v : Val}
      (hv : [linVecVal m, encIntMatrix A, encIntMatrix B][i]? = some v) :=
    Det.arg' (P := P) (vs := [linVecVal m, encIntMatrix A, encIntMatrix B]) (rest := rest) (j := i) hv
  have dn := Det.length (da 0 [] rfl)
  simp only [List.length_map, List.length_finRange] at dn
  have dm := Det.call (Det.mk2 (Det.mk2 dn (da 2 [] rfl)) (da 1 [] rfl)) hs
  have dr := Det.call (Det.mk2 (da 0 [encIntMatrix (A * B)] rfl)
    (Det.var' (P := P) (env := [a, encIntMatrix (A * B)]) (i := 1) rfl)) hr
  apply FunDet.intro hp.entry
  refine (Det.letE dm dr).mono ?_
  unfold linFiniteProductCost
  dsimp only [a, W, MC, RC, linFiniteProductReduceBudget, linFiniteProductMulBudget,
    linVecVal, encIntMatrix] at *
  omega

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem linFiniteProductCost_poly : PBU (fun n W _ => linFiniteProductCost W n) := by
  simp only [linFiniteProductCost, linFiniteProductMulBudget, linFiniteProductReduceBudget,
    linFiniteMatrixReduceCost, linFiniteMatrixReduceStepCost, linFiniteMatrixReduceAcc,
    linFiniteMatrixReduceRowBudget, linConstRemCost, linMapBudget, linScalarRemCost,
    linMatrixMulCost, linMatrixMulRowCost, linRowMulCost, linRowMulStepCost, linRowMulEntryWt,
    linRowMulDotIn, linRowMulColWt, linRowMulColIn, linColumnCost, linDotLoopCost, linDotStepCost,
    linDotProductWt, linDotAccWt, linVectorAccWt, linIntBinaryCost, linIntCoreBudget,
    linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
