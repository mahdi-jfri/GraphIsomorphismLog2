import Workspace.Impl.LinMapEncoded
import Workspace.Impl.LinSumPerm
import Workspace.Lang.Lib.LinIntColumn
import Workspace.Impl.LinIntPoly

/-! A dense integer matrix applied to a column vector, using the proved
shared-entry integer dot-product program on each matrix row. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linMatrixVecRowF (dot : ℕ) : Expr := .call dot (mk3 (arg 0) (arg 1) linIntZeroE)

def linMatrixVecFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [linMatrixVecRowF (b + 4)] ++
    linDotLoopFuns (b + 4) (b + 7) ++ linIntFuns (b + 7)

theorem linMatrixVecFuns_length (b : ℕ) : (linMatrixVecFuns b).length = 25 := rfl

structure linMatrixVecAt (P : Program) (b : ℕ) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  row : P.funs[b + 3]? = some (linMatrixVecRowF (b + 4))
  dot : P.HasAt (b + 4) (linDotLoopFuns (b + 4) (b + 7))
  ints : linIntSpec P (b + 7)

theorem linMatrixVecAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linMatrixVecFuns b)) : linMatrixVecAt P b where
  map := h.block 0 rfl
  row := (h.block (gs := [linMatrixVecRowF (b + 4)]) 3 rfl).single
  dot := h.block 4 rfl
  ints := linInt_spec (h.block 7 rfl)

def linMatrixVecRowCost (W r : ℕ) : ℕ := 10000 * (W + linDotLoopCost (100 * (W + 1)) r + 1)
def linMatrixVecCost (W r : ℕ) : ℕ := linMapBudget W (linMatrixVecRowCost (100 * (W + 1)) r)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linMatrixVecRow_spec {P : Program} {b r : ℕ} (h : linMatrixVecAt P b) (x y : Fin r → ℤ) :
    FunDet P (b + 3) (.list [linVecVal x, linVecVal y]) (encInt (∑ j, x j * y j))
      (linMatrixVecRowCost (Val.list [linVecVal x, linVecVal y]).wt r) := by
  let a := Val.list [linVecVal x, linVecVal y]
  let W := a.wt
  have wx : (linVecVal x).wt < W := wt_le_wt_list (by simp [W, a])
  have wy : (linVecVal y).wt < W := wt_le_wt_list (by simp [W, a])
  have wz : (encInt 0).wt ≤ 20 := by decide
  have wi := wt_list3_le (linVecVal x) (linVecVal y) (encInt 0)
  have warg : (Val.list [linVecVal x, linVecVal y, encInt 0]).wt ≤ 100 * (W + 1) := by omega
  have hh := (linDotLoop_spec h.ints h.dot x y).mono (linDotLoopCost_mono warg r)
  have dx := Det.arg' (P := P) (vs := [linVecVal x, linVecVal y]) (rest := []) (j := 0) rfl
  have dy := Det.arg' (P := P) (vs := [linVecVal x, linVecVal y]) (rest := []) (j := 1) rfl
  have dz : Det P [a] linIntZeroE (encInt 0) 100 := (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  apply FunDet.intro h.row
  refine (Det.call (Det.mk3 dx dy dz) hh).mono ?_
  have wo := hh.wt_lt.le
  change _ ≤ linMatrixVecRowCost W r
  unfold linMatrixVecRowCost
  dsimp only [a, W] at *
  omega

theorem linMatrixVecRowCost_mono {W V r s : ℕ} (hW : W ≤ V) (hr : r ≤ s) :
    linMatrixVecRowCost W r ≤ linMatrixVecRowCost V s := by
  simp only [linMatrixVecRowCost, linDotLoopCost, linDotStepCost, linDotAccWt, linDotProductWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linMatrixVec_spec {P : Program} {b m r : ℕ} (h : linMatrixVecAt P b)
    (A : Matrix (Fin m) (Fin r) ℤ) (x : Fin r → ℤ) :
    FunDet P b (.list [linVecVal x, encIntMatrix A]) (linVecVal (A.mulVec x))
      (linMatrixVecCost (Val.list [linVecVal x, encIntMatrix A]).wt r) := by
  let a := Val.list [linVecVal x, encIntMatrix A]
  let W := a.wt
  have wx : (linVecVal x).wt < W := wt_le_wt_list (by simp [W, a])
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [W, a])
  have hf (y : Fin r → ℤ) (hy : y ∈ (List.finRange m).map A) :
      FunDet P (b + 3) (.list [linVecVal x, linVecVal y]) (encInt (∑ j, x j * y j))
        (linMatrixVecRowCost (100 * (W + 1)) r) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    have wy : (linVecVal (A i)).wt < (encIntMatrix A).wt := wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have wi := wt_list2_le (linVecVal x) (linVecVal (A i))
    refine (linMatrixVecRow_spec h x (A i)).mono (linMatrixVecRowCost_mono ?_ le_rfl)
    omega
  have hh := linMapEncoded_spec h.map linVecVal linVecVal_injective
    (fun y : Fin r → ℤ => encInt (∑ j, x j * y j)) (linVecVal x) ((List.finRange m).map A)
    (linMatrixVecRowCost (100 * (W + 1)) r) hf
  have he (i : Fin m) : (∑ j, x j * A i j) = A.mulVec x i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  simpa only [linVecVal, encIntMatrix, List.map_map, Function.comp_def, he, linMatrixVecCost, a, W] using hh

theorem linMatrixVecCost_mono {W V r s : ℕ} (hW : W ≤ V) (hr : r ≤ s) :
    linMatrixVecCost W r ≤ linMatrixVecCost V s := by
  apply linMapBudget_mono hW
  exact linMatrixVecRowCost_mono (by omega) hr

theorem linMatrixVecCost_poly : PBU (fun r W _ => linMatrixVecCost W r) := by
  simp only [linMatrixVecCost, linMapBudget, linMatrixVecRowCost, linDotLoopCost,
    linDotStepCost, linDotAccWt, linDotProductWt, linIntBinaryCost, linIntCoreBudget,
    linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
