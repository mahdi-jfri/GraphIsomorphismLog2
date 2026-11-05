module

public import Workspace.Impl.LinPrimaryOffset
public import Workspace.Impl.LinPrimaryMatrixFull
public import Workspace.Impl.LinMapSource

@[expose] public section

/-! Reduce one retained full affine record to its field-layer matrix and
translation. This is the scalar operation used on the current cover generators. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryMatrixFullCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryMatrixFullCost W ≤ linPrimaryMatrixFullCost V := by
  simp only [linPrimaryMatrixFullCost, linPrimaryMatrixFullModBudget, linPrimaryMatrixFullArg,
    linPrimaryMatrixFullBuildBudget, linModMatrixCost, linModVectorCost, linModReduceCost,
    linIntCodecCost, linPrimaryMatrixCost, linPrimaryMatrixRowCost, linTabulateCost,
    linTabulateRangeCost, linMapBudget]
  gcongr

theorem linPrimaryOffsetCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryOffsetCost W ≤ linPrimaryOffsetCost V := by
  simp only [linPrimaryOffsetCost, linPrimaryOffsetColumnBudget, linPrimaryOffsetArg,
    linPrimaryOffsetVectorBudget, linColumnCost, linVectorAccWt, linPrimaryVectorCost,
    linPrimaryVectorCellCost, linPrimaryDigitCost, linIntCodecCost, linTabulateCost,
    linTabulateRangeCost, linMapBudget]
  gcongr

def linPrimaryRecordF (matrix offset : ℕ) : Expr :=
  .letE (.call matrix (mk4 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))))
    (.letE (.call offset (mk4 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 1))))
      (mk2 (.var 1) (.var 2)))

def linPrimaryRecordFuns (b : ℕ) : List Expr :=
  [linPrimaryRecordF (b + 1) (b + 44)] ++ linPrimaryMatrixFullFuns (b + 1) ++ linPrimaryOffsetFuns (b + 44)

theorem linPrimaryRecordFuns_length (b : ℕ) : (linPrimaryRecordFuns b).length = 77 := rfl

structure linPrimaryRecordAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryRecordF (b + 1) (b + 44))
  matrix : linPrimaryMatrixFullAt P (b + 1)
  offset : linPrimaryOffsetAt P (b + 44)

theorem linPrimaryRecordAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryRecordFuns b)) : linPrimaryRecordAt P b where
  entry := (h.block (gs := [linPrimaryRecordF (b + 1) (b + 44)]) 0 rfl).single
  matrix := linPrimaryMatrixFullAt_of (h.block 1 rfl)
  offset := linPrimaryOffsetAt_of (h.block 44 rfl)

def linPrimaryRecordCost (W : ℕ) : ℕ := 100000 * (W +
  linPrimaryMatrixFullCost (100 * (W + 1)) + linPrimaryOffsetCost (100 * (W + 1)) + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linPrimaryRecord_spec {P : Program} {b p d : ℕ} (h : linPrimaryRecordAt P b)
    (hp : p.Prime) (ν : Fin d → ℕ) (level : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (u : linFiniteVec (linPrimaryOrders p ν)) (inv : Val) :
    let m := linPrimaryOrders p ν
    let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
    let ctx := Val.list [.nat p, encFun ν, .nat level, .nat (p ^ level)]
    let a := Val.list [ctx, record]
    FunDet P b a (.list [encModMatrix (linPrimaryFieldMatrix p ν level f), encVec (linPrimaryCoord p ν level u)])
      (linPrimaryRecordCost a.wt) := by
  let m := linPrimaryOrders p ν
  let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
  let ctx := Val.list [.nat p, encFun ν, .nat level, .nat (p ^ level)]
  let a := Val.list [ctx, record]
  let W := a.wt
  let mat := encModMatrix (linPrimaryFieldMatrix p ν level f)
  let vec := encVec (linPrimaryCoord p ν level u)
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wr : record.wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wν : (encFun ν).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wl : (Val.nat level).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wq : (Val.nat (p ^ level)).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wmarg : (Val.list [record, .nat p, encFun ν, .nat level]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list4_le record (.nat p) (encFun ν) (.nat level)
    omega
  have woarg : (Val.list [record, .nat p, .nat (p ^ level), encFun ν]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list4_le record (.nat p) (.nat (p ^ level)) (encFun ν)
    omega
  have hm := (linPrimaryMatrixFull_spec h.matrix hp ν level f u inv).mono (linPrimaryMatrixFullCost_mono wmarg)
  have ho := (linPrimaryOffset_spec h.offset hp.pos ν level f u inv).mono (linPrimaryOffsetCost_mono woarg)
  have wmat := hm.wt_lt.le
  have wvec := ho.wt_lt.le
  have dc := Det.arg' (P := P) (vs := [ctx, record]) (rest := []) (j := 0) rfl
  have dr := Det.arg' (P := P) (vs := [ctx, record]) (rest := []) (j := 1) rfl
  have dp := Det.get' dc (Det.nat 0) rfl
  have dν := Det.get' dc (Det.nat 1) rfl
  have dl := Det.get' dc (Det.nat 2) rfl
  have dm := Det.call (Det.mk4 dr dp dν dl) hm
  have dc' := Det.arg' (P := P) (vs := [ctx, record]) (rest := [mat]) (j := 0) rfl
  have dr' := Det.arg' (P := P) (vs := [ctx, record]) (rest := [mat]) (j := 1) rfl
  have dp' := Det.get' dc' (Det.nat 0) rfl
  have dq' := Det.get' dc' (Det.nat 3) rfl
  have dν' := Det.get' dc' (Det.nat 1) rfl
  have do' := Det.call (Det.mk4 dr' dp' dq' dν') ho
  have dout := Det.mk2
    (Det.var' (P := P) (env := [a, mat, vec]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, mat, vec]) (i := 2) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dm (Det.letE do' dout)).mono ?_
  have wout := wt_list2_le mat vec
  have wma := wt_list4_le record (.nat p) (encFun ν) (.nat level)
  have woa := wt_list4_le record (.nat p) (.nat (p ^ level)) (encFun ν)
  change _ ≤ linPrimaryRecordCost W
  unfold linPrimaryRecordCost
  dsimp only [a, W, mat, vec, ctx, record] at *
  omega

theorem linPrimaryRecordCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryRecordCost W ≤ linPrimaryRecordCost V := by
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h
    (linPrimaryMatrixFullCost_mono (by omega))) (linPrimaryOffsetCost_mono (by omega))) 1

theorem linPrimaryRecordCost_poly : PBU (fun _ W _ => linPrimaryRecordCost W) := by
  have hm := linPoly_subst linPrimaryMatrixFullCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ho := linPoly_subst linPrimaryOffsetCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hm) ho) 1)

end GI.Impl
