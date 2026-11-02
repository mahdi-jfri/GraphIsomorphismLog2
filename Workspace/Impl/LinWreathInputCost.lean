import Workspace.Impl.LinWreathInputProg

namespace GI.Impl
open GI.Cited GI.Lang

def linWreathInputPermBudget (W : ℕ) : ℕ := linWreathPermCost (100 * (W + 1)) W
def linWreathInputGroupBudget (W : ℕ) : ℕ := mkGroupK * ((2 * W + 3) * (2 * W + 1)) ^ 3
def linWreathInputMatrixBudget (W : ℕ) : ℕ := linWreathMatricesCost (100 * (W + 1)) W
def linWreathInputVectorBudget (W : ℕ) : ℕ := 100000 * (W + 1) ^ 2

def linWreathInputSum (W : ℕ) : ℕ := W + linTailCost W + linWreathInputPermBudget W +
  linWreathInputGroupBudget W + linWreathInputMatrixBudget W + linWreathInputVectorBudget W + 1

def linWreathInputCost (W : ℕ) : ℕ := 1000000 * linWreathInputSum W

theorem linWreathPermCost_mono {W V n m : ℕ} (hW : W ≤ V) (hn : n ≤ m) :
    linWreathPermCost W n ≤ linWreathPermCost V m := by
  simp only [linWreathPermCost, linWreathPermMapCost, linWreathPermAppendCost, linWreathPermWt,
    linWreathCopyCost, linSumPermCost, linSumPermMapBudget, linSumPermAppendBudget,
    linSwapPermCost, linSwapPermRangeBudget, linSwapPermMapBudget, linMapBudget]
  gcongr

theorem linWreathMatricesCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linWreathMatricesCost W d ≤ linWreathMatricesCost V e := by
  simp only [linWreathMatricesCost, linWreathMatricesAppendCost, linWreathMatricesMapCost,
    linWreathMatricesSwapCost, linZeroModMatrixCost, linWreathMatrixItemCost,
    linWreathBlockCost, linWreathBlockRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

theorem linWreathInputCost_poly : PBU (fun _ W _ => linWreathInputCost W) := by
  simp only [linWreathInputCost, linWreathInputSum, linWreathInputPermBudget,
    linWreathInputGroupBudget, linWreathInputMatrixBudget, linWreathInputVectorBudget,
    linTailCost, mkGroupK, linWreathPermCost, linWreathPermMapCost, linWreathPermAppendCost,
    linWreathPermWt, linWreathCopyCost, linSumPermCost, linSumPermMapBudget,
    linSumPermAppendBudget, linSwapPermCost, linSwapPermRangeBudget, linSwapPermMapBudget,
    linWreathMatricesCost, linWreathMatricesAppendCost, linWreathMatricesMapCost,
    linWreathMatricesSwapCost, linZeroModMatrixCost, linWreathMatrixItemCost,
    linWreathBlockCost, linWreathBlockRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
