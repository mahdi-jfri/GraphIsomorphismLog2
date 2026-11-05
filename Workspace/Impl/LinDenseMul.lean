module

public import Workspace.Lang.Lib.LinIntMatrix
public import Workspace.Impl.LinIntPoly

@[expose] public section

/-! A concrete self-contained layout of the proved dense integer product. -/
namespace GI.Impl
open GI.Lang GI.Cited

def linDenseMulFuns (b : ℕ) : List Expr :=
  linMatrixMulFuns b (b + 4) ++ linRowMulFuns (b + 4) (b + 7) (b + 11) ++
    linColumnFuns (b + 7) ++ linDotLoopFuns (b + 11) (b + 14) ++ linIntFuns (b + 14)

theorem linDenseMulFuns_length (b : ℕ) : (linDenseMulFuns b).length = 32 := rfl

structure linDenseMulAt (P : Program) (b : ℕ) : Prop where
  matrix : P.HasAt b (linMatrixMulFuns b (b + 4))
  row : P.HasAt (b + 4) (linRowMulFuns (b + 4) (b + 7) (b + 11))
  column : P.HasAt (b + 7) (linColumnFuns (b + 7))
  dot : P.HasAt (b + 11) (linDotLoopFuns (b + 11) (b + 14))
  ints : linIntSpec P (b + 14)

theorem linDenseMulAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linDenseMulFuns b)) : linDenseMulAt P b where
  matrix := h.block 0 rfl
  row := h.block 4 rfl
  column := h.block 7 rfl
  dot := h.block 11 rfl
  ints := linInt_spec (h.block 14 rfl)

theorem linDenseMul_spec {P : Program} {b m r c : ℕ} (hp : linDenseMulAt P b)
    (A : Matrix (Fin m) (Fin r) ℤ) (B : Matrix (Fin r) (Fin c) ℤ) :
    FunDet P b (.list [.list [.nat c, encIntMatrix B], encIntMatrix A]) (encIntMatrix (A * B))
      (linMatrixMulCost (Val.list [.list [.nat c, encIntMatrix B], encIntMatrix A]).wt m r c) :=
  linMatrixMul_spec hp.ints hp.matrix hp.row hp.column hp.dot A B

theorem linDenseMulCost_mono {W V m r c : ℕ} (hW : W ≤ V) :
    linMatrixMulCost W m r c ≤ linMatrixMulCost V m r c := by
  dsimp only [linMatrixMulCost, linMatrixMulRowCost, linRowMulCost, linRowMulStepCost,
    linRowMulEntryWt, linRowMulDotIn, linRowMulColWt, linRowMulColIn, linColumnCost,
    linDotLoopCost, linDotStepCost, linDotProductWt, linDotAccWt, linVectorAccWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  gcongr

theorem linDenseMulCost_poly : PBU (fun n W _ => linMatrixMulCost W n n n) := by
  dsimp only [linMatrixMulCost, linMatrixMulRowCost, linRowMulCost, linRowMulStepCost,
    linRowMulEntryWt, linRowMulDotIn, linRowMulColWt, linRowMulColIn, linColumnCost,
    linDotLoopCost, linDotStepCost, linDotProductWt, linDotAccWt, linVectorAccWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
