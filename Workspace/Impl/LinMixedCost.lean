module

public import Workspace.Impl.LinMixedArg

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

noncomputable def linMixedPassCoefficient (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimePassCost_poly hm hv)).choose
noncomputable def linMixedPassDegree (hm : ConstructiveMembership) (hv : VectorStabilizer) : ℕ :=
  (linPoly_source_bound (linPrimePassCost_poly hm hv)).choose_spec.choose
noncomputable def linMixedCallBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  linMixedPassCoefficient hm hv * (linMixedIterationWeight W + 1) ^ linMixedPassDegree hm hv

def linMixedPrimeBudget (W : ℕ) : ℕ := linPrimeTestCost W

def linMixedPrimeCallBudget (W S : ℕ) : ℕ := 100000 * (S + W + linMixedPrimeBudget W + 1)
noncomputable def linMixedStepBudget (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  10000000000 * (W + linPrimaryAccumulatorWeight W + linMixedCallBudget hm hv W + linMixedPrimeBudget W + 1)
noncomputable def linMixedLoopCost (hm : ConstructiveMembership) (hv : VectorStabilizer) (W : ℕ) : ℕ :=
  1000000 * (linMixedInitBudget W + W * linMixedStepBudget hm hv W +
    1000 * (W + 1) * (2 * W + linPrimaryAccumulatorWeight W + 1) + 1)

theorem linMixedCallBudget_bound (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {W input : ℕ} (h : input ≤ linMixedIterationWeight W) :
    linPrimePassCost hm hv input ≤ linMixedCallBudget hm hv W :=
  (linPoly_source_bound (linPrimePassCost_poly hm hv)).choose_spec.choose_spec 0 input
    (linMixedIterationWeight W) (Nat.zero_le _) h

theorem linMixedStepBudget_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linMixedStepBudget hm hv W) := by
  have hc : PBU (fun _ W _ => linMixedCallBudget hm hv W) :=
    PBU.smul _ (PBU.pow (PBU.addc linMixedIterationWeight_poly 1) _)
  have hp : PBU (fun _ W _ => linMixedPrimeBudget W) := by
    unfold linMixedPrimeBudget linPrimeTestCost
    norm_poly
  exact PBU.smul 10000000000 (PBU.addc (PBU.add
    (PBU.add (PBU.add PBU.W linPrimaryAccumulatorWeight_poly) hc) hp) 1)

theorem linMixedLoopCost_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun _ W _ => linMixedLoopCost hm hv W) := by
  have hi : PBU (fun _ W _ => linMixedInitBudget W) := by unfold linMixedInitBudget; norm_poly
  simpa only [linMixedLoopCost, Nat.mul_assoc] using PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add hi
    (PBU.mul PBU.W (linMixedStepBudget_poly hm hv)))
    (PBU.smul 1000 (PBU.mul (PBU.addc PBU.W 1)
      (PBU.addc (PBU.add (PBU.smul 2 PBU.W) linPrimaryAccumulatorWeight_poly) 1)))) 1)

end GI.Impl
