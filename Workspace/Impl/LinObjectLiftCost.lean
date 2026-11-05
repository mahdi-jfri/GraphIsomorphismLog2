module

public import Workspace.Impl.LinObjectLift
public import Workspace.Impl.LinPermWordImage

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectLiftBuildCoefficient : ℕ := linObjectQuotientBuildCost_poly.choose
noncomputable def linObjectLiftBuildDegree : ℕ := linObjectQuotientBuildCost_poly.choose_spec.choose
noncomputable def linObjectLiftBuildBudget (W : ℕ) : ℕ :=
  linObjectLiftBuildCoefficient * (100 * (W + 1) + 2) ^ linObjectLiftBuildDegree

def linObjectLiftNegBudget (W : ℕ) : ℕ := linVectorScaleCost (100 * (W + 1)) W

noncomputable def linObjectLiftSolveCoefficient (hH : HermiteFullRank) : ℕ :=
  (linRowSolverBudget_poly hH).choose
noncomputable def linObjectLiftSolveDegree (hH : HermiteFullRank) : ℕ :=
  (linRowSolverBudget_poly hH).choose_spec.choose
noncomputable def linObjectLiftSolveArg (W : ℕ) : ℕ :=
  100 * (W + linObjectLiftBuildBudget W + linObjectLiftNegBudget W + 1)
noncomputable def linObjectLiftSolveBudget (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  linObjectLiftSolveCoefficient hH * (linObjectLiftSolveArg W + 2) ^ linObjectLiftSolveDegree hH

noncomputable def linObjectLiftSliceArg (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectLiftBuildBudget W + linObjectLiftSolveBudget hH W + 1)
noncomputable def linObjectLiftSliceBudget (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  linSliceCost (linObjectLiftSliceArg hH W)
noncomputable def linObjectLiftWordArg (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  100 * (W + linObjectLiftSliceBudget hH W + 1)
noncomputable def linObjectLiftWordBudget (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  linPermWordCost (linObjectLiftWordArg hH W)

noncomputable def linObjectLiftCost (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  100000000 * ((W + 1) ^ 2 + W + linObjectLiftBuildBudget W + linObjectLiftNegBudget W +
    linObjectLiftSolveBudget hH W + linObjectLiftSliceBudget hH W + linObjectLiftWordBudget hH W + 1)

theorem linObjectLiftBuild_bound {U W : ℕ} (hU : U ≤ 100 * (W + 1)) :
    linObjectQuotientBuildCost U ≤ linObjectLiftBuildBudget W := by
  have hh := linObjectQuotientBuildCost_poly.choose_spec.choose_spec 0 U 0
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem linObjectLiftSolve_bound (hH : HermiteFullRank) (I : FullRankInst) (w : Fin I.c → ℤ)
    (W : ℕ) (harg : (Val.list [fullRankInput I, linVecVal w]).wt ≤ linObjectLiftSolveArg W) :
    linRowSolverCost hH I (Val.list [fullRankInput I, linVecVal w]).wt ≤
      linObjectLiftSolveBudget hH W := by
  have hh := (linRowSolverBudget_poly hH).choose_spec.choose_spec
    0 (Val.list [fullRankInput I, linVecVal w]).wt 0
  exact (linRowSolverCost_le hH I w).trans (hh.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))

theorem linSliceCost_mono {W V : ℕ} (hW : W ≤ V) : linSliceCost W ≤ linSliceCost V := by
  unfold linSliceCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 3)

theorem linPermWordCost_mono {W V : ℕ} (hW : W ≤ V) : linPermWordCost W ≤ linPermWordCost V := by
  simp only [linPermWordCost, linPermWordAcc, linPermWordArg, linPermZpowCost, linIntCodecCost,
    linPermPowCost, linPermPowUnit]
  gcongr

theorem linObjectLiftBuildBudget_poly : PBU (fun _ W _ => linObjectLiftBuildBudget W) := by
  unfold linObjectLiftBuildBudget
  norm_poly

theorem linObjectLiftNegBudget_poly : PBU (fun _ W _ => linObjectLiftNegBudget W) := by
  simp only [linObjectLiftNegBudget, linVectorScaleCost, linVectorAccWt, linIntBinaryCost,
    linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

theorem linObjectLiftCost_poly (hH : HermiteFullRank) : PBU (fun _ W _ => linObjectLiftCost hH W) := by
  have hb := linObjectLiftBuildBudget_poly
  have hn := linObjectLiftNegBudget_poly
  have ha : PBU (fun _ W _ => linObjectLiftSolveArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add (PBU.add PBU.W hb) hn) 1)
  have hr : PBU (fun _ W _ => linObjectLiftSolveBudget hH W) :=
    PBU.smul (linObjectLiftSolveCoefficient hH)
      (PBU.pow (PBU.addc ha 2) (linObjectLiftSolveDegree hH))
  have hsa : PBU (fun _ W _ => linObjectLiftSliceArg hH W) :=
    PBU.smul 100 (PBU.addc (PBU.add (PBU.add PBU.W hb) hr) 1)
  have hs : PBU (fun _ W _ => linObjectLiftSliceBudget hH W) :=
    linPoly_subst (f := fun _ W _ => linSliceCost W) linSliceCost_poly
      (PBU.const 0) hsa (PBU.const 0)
  have hwa : PBU (fun _ W _ => linObjectLiftWordArg hH W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hs) 1)
  have hw : PBU (fun _ W _ => linObjectLiftWordBudget hH W) :=
    linPoly_subst (f := fun _ W _ => linPermWordCost W) linPermWordCost_poly
      (PBU.const 0) hwa (PBU.const 0)
  exact PBU.smul 100000000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.add (PBU.pow (PBU.addc PBU.W 1) 2) PBU.W) hb) hn) hr) hs) hw) 1)

end GI.Impl
