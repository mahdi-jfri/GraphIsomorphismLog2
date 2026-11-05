module

public import Workspace.Impl.LinWreathPermData
public import Workspace.Lang.Lib.LinIntTail

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathCopyF (sum : ℕ) (first : Bool) : Expr :=
  .call sum (if first then mk2 (arg 1) (arg 0) else mk2 (arg 0) (arg 1))

def linWreathCopyCost (W : ℕ) : ℕ :=
  10000 * (W + linSumPermCost (100 * (W + 1)) + 1)

theorem linSumPermCost_mono {W V : ℕ} (h : W ≤ V) : linSumPermCost W ≤ linSumPermCost V := by
  unfold linSumPermCost linSumPermMapBudget linSumPermAppendBudget linMapBudget
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linWreathCopy_spec {P : Program} {f sum n : ℕ} (first : Bool)
    (hf : P.funs[f]? = some (linWreathCopyF sum first))
    (hp : P.HasAt sum (linSumPermFuns sum)) (g : Perm (Fin n)) :
    FunDet P f (.list [encPerm (1 : Perm (Fin n)), encPerm g])
      (encPerm (sumToFin (if first then Equiv.sumCongr g 1 else Equiv.sumCongr 1 g)))
      (linWreathCopyCost (Val.list [encPerm (1 : Perm (Fin n)), encPerm g]).wt) := by
  let a := Val.list [encPerm (1 : Perm (Fin n)), encPerm g]
  let W := a.wt
  have w₁ : (encPerm (1 : Perm (Fin n))).wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp [W, a])
  have hrev : (Val.list [encPerm g, encPerm (1 : Perm (Fin n))]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encPerm g) (encPerm (1 : Perm (Fin n)))
    omega
  have harg : a.wt ≤ 100 * (W + 1) := by change W ≤ _; omega
  have d₁ := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin n)), encPerm g]) (rest := []) (j := 0) rfl
  have dg := Det.arg' (P := P) (vs := [encPerm (1 : Perm (Fin n)), encPerm g]) (rest := []) (j := 1) rfl
  cases first
  · have hh := (linSumPerm_spec hp 1 g).mono (linSumPermCost_mono harg)
    have dd := Det.call (Det.mk2 d₁ dg) hh
    apply FunDet.intro hf
    refine dd.mono ?_
    have wo := hh.wt_lt.le
    have wi := wt_list2_le (encPerm (1 : Perm (Fin n))) (encPerm g)
    change _ ≤ linWreathCopyCost W
    dsimp only [linWreathCopyCost]
    dsimp only [a, W] at *
    omega
  · have hh := (linSumPerm_spec hp g 1).mono (linSumPermCost_mono hrev)
    have dd := Det.call (Det.mk2 dg d₁) hh
    apply FunDet.intro hf
    refine dd.mono ?_
    have wo := hh.wt_lt.le
    have wi := wt_list2_le (encPerm g) (encPerm (1 : Perm (Fin n)))
    change _ ≤ linWreathCopyCost W
    dsimp only [linWreathCopyCost]
    dsimp only [a, W] at *
    omega

theorem linWreathCopyCost_mono {W V : ℕ} (h : W ≤ V) :
    linWreathCopyCost W ≤ linWreathCopyCost V := by
  unfold linWreathCopyCost linSumPermCost linSumPermMapBudget linSumPermAppendBudget linMapBudget
  gcongr

theorem linWreathCopyCost_poly : PBU (fun _ W _ => linWreathCopyCost W) := by
  unfold linWreathCopyCost linSumPermCost linSumPermMapBudget linSumPermAppendBudget linMapBudget
  norm_poly

end GI.Impl
