module

public import Workspace.Impl.LinPrimePrepare

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linTrialPrepareCost_mono {W V : ℕ} (h : W ≤ V) :
    linTrialPrepareCost W ≤ linTrialPrepareCost V := by
  unfold linTrialPrepareCost linTrialPrepareSplitBudget linPairColumnsCost linPairColumnsBudget
    linTrialFactorsCost linMapBudget linTrialFactorCost linTrialExponentCost
    linTrialExponentBudget linTrialExponentArg linTrialFactorPower linTrialFactorEncode
    linNatPowerCost linTrialPrimaryCost linIntCodecCost
  gcongr

theorem linPrimeContextCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimeContextCost W ≤ linPrimeContextCost V := by
  have hs := linPrimeRecordCost_mono (by omega : 100 * (W + 1) ≤ 100 * (V + 1))
  have hm : linPrimeContextMapBudget W ≤ linPrimeContextMapBudget V := by
    simp only [linPrimeContextMapBudget, linPrimeContextCellBudget, linMapBudget]
    gcongr
  unfold linPrimeContextCost linPrimeContextCellBudget
  omega

theorem linPrimePointCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimePointCost W ≤ linPrimePointCost V := linFinitePointReduceCost_mono h h

theorem linPrimePrepareCost_poly : PBU (fun _ W _ => linPrimePrepareCost W) := by
  have ht := linPoly_subst linTrialPrepareCost_poly (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linPrimePrepareSubArg W) :=
    PBU.smul 1000 (PBU.addc (PBU.add PBU.W ht) 1)
  have hc := linPoly_subst linPrimeContextCost_poly (PBU.const 0) ha (PBU.const 0)
  have hp := linPoly_subst linPrimePointCost_poly (PBU.const 0) ha (PBU.const 0)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W ht) hc) hp) 1)

end GI.Impl
