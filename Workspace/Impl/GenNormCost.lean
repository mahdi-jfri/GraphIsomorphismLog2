module

public import Workspace.Impl.GenNormIncProg
public import Workspace.Impl.GenNormOrbit
public import Workspace.Impl.GenCost

@[expose] public section

/-!
# The incidence-test budget

The point-incidence test has a cubic own cost. With a polynomial input weight and point
degree at most `N`, it fits the general dispatcher's `exp(A log²(N+2))` budget.
-/

namespace GI.Impl

open GI.Lang GI.Paper GI.Algorithm

/-- The bound in `normIncTest_spec` is uniformly polynomial in the input weight and degree. -/
theorem normIncCost_poly :
    PBU (fun m W _ => 10000000 * (W + m + 1) ^ 3) :=
  PBU.smul 10000000 (PBU.pow (PBU.addc (PBU.add PBU.W PBU.k) 1) 3)

/-- The incidence test fits `E_N` for every fixed polynomial bound on its input weight. -/
theorem normIncCost_le_expLogSq (a d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m W N : ℕ, m ≤ N → W ≤ a * (N + 2) ^ d →
      (10000000 * (W + m + 1) ^ 3 : ℕ) ≤ expLogSq A N := by
  obtain ⟨A, hA, h⟩ := normIncCost_poly.le_expLogSq a d 0
  exact ⟨A, hA, fun m W N hm hW => h m W 0 N hm hW (Nat.zero_le _)⟩

/-- The mode test is polynomial in the position degree and input weight. -/
theorem normOrbitCost_poly : PBU (fun k W _ => normOrbitCost k W) :=
  PBU.add (PBU.add (PBU.smul loK (PBU.pow PBU.k1 15))
    (PBU.smul maxK (PBU.pow PBU.k1 3)))
    (PBU.smul 1000 (PBU.addc (PBU.add PBU.W PBU.k) 1))

/-- The orbit computation also fits `E_N` for polynomial input weight. -/
theorem normOrbitCost_le_expLogSq (a d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k W N : ℕ, k ≤ N → W ≤ a * (N + 2) ^ d →
      (normOrbitCost k W : ℝ) ≤ expLogSq A N := by
  obtain ⟨A, hA, h⟩ := normOrbitCost_poly.le_expLogSq a d 0
  exact ⟨A, hA, fun k W N hk hW => h k W 0 N hk hW (Nat.zero_le _)⟩

end GI.Impl
