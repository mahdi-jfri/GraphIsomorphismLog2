module

public import Workspace.Impl.LinWreathBlockProg
public import Workspace.Lang.Prims.Other

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linWreathMatrixItemF (block : ℕ) : Expr := .call block (mk2 (arg 1) (arg 0))
def linWreathMatrixItemCost (W d : ℕ) : ℕ :=
  10000 * (W + linWreathBlockCost (100 * (W + 1)) d + 1)

theorem linWreathBlockCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linWreathBlockCost W d ≤ linWreathBlockCost V e := by
  simp only [linWreathBlockCost, linWreathBlockRowCost, linTabulateCost, linTabulateRangeCost,
    linMapBudget]
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linWreathMatrixItem_spec {P : Program} {f block p d : ℕ}
    (hf : P.funs[f]? = some (linWreathMatrixItemF block)) (hb : linWreathBlockAt P block)
    (hp : p.Prime) (hd : 0 < d) (A : Matrix (Fin d) (Fin d) (ZMod p)) (mode : Fin 3) :
    FunDet P f (.list [.nat mode, encModMatrix A]) (encModMatrix (linWreathBlock hd A mode))
      (linWreathMatrixItemCost (Val.list [.nat mode, encModMatrix A]).wt d) := by
  let a := Val.list [.nat mode, encModMatrix A]
  let W := a.wt
  have wa : (encModMatrix A).wt < W := wt_le_wt_list (by simp [W, a])
  have wm : (Val.nat mode).wt < W := wt_le_wt_list (by simp [W, a])
  have warg : (Val.list [encModMatrix A, .nat mode]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encModMatrix A) (.nat mode)
    omega
  have hh := (linWreathBlock_spec hb hp hd A mode).mono (linWreathBlockCost_mono warg le_rfl)
  have da := Det.arg' (P := P) (vs := [.nat mode, encModMatrix A]) (rest := []) (j := 1) rfl
  have dm := Det.arg' (P := P) (vs := [.nat mode, encModMatrix A]) (rest := []) (j := 0) rfl
  apply FunDet.intro hf
  refine (Det.call (Det.mk2 da dm) hh).mono ?_
  have wo := hh.wt_lt.le
  have ww := wt_list2_le (encModMatrix A) (.nat mode)
  change _ ≤ linWreathMatrixItemCost W d
  dsimp only [linWreathMatrixItemCost]
  dsimp only [W, a] at *
  omega

theorem linWreathMatrixItemCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linWreathMatrixItemCost W d ≤ linWreathMatrixItemCost V e := by
  simp only [linWreathMatrixItemCost, linWreathBlockCost, linWreathBlockRowCost,
    linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

end GI.Impl
