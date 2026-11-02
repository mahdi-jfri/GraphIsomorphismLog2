import Mathlib.GroupTheory.SpecificGroups.Alternating
import Lean.Elab.Tactic.Omega

namespace GI

variable {V : Type*}

/-- A concrete visible alternating quotient on the active orbit of `a`.
The homomorphism kernel is exactly the supplied lower subgroup. -/
structure VisibleStep (a : V) (H L : Subgroup (Equiv.Perm V)) (k : ℕ) where
  lower : L ≤ H
  quotient : H →* alternatingGroup (Fin k)
  onto : Function.Surjective quotient
  kernel : ∀ h : H, quotient h = 1 ↔ (h : Equiv.Perm V) ∈ L
  transitiveKernel : ∀ h : H, ∃ l : L, (l : Equiv.Perm V) a = (h : Equiv.Perm V) a
  visible : ∀ h : H,
    (∀ g : H, (h : Equiv.Perm V) ((g : Equiv.Perm V) a) = (g : Equiv.Perm V) a) → quotient h = 1

/-- Finite chains with arbitrary subgroup restrictions and visible marked steps.
The active point is fixed; its subgroup orbits are implicit in `VisibleStep`. -/
inductive MarkedChain (cutoff : ℕ) (a : V) :
    Subgroup (Equiv.Perm V) → ℕ → Prop
  | stop (H) : MarkedChain cutoff a H 0
  | restrict {H L w} : L ≤ H → MarkedChain cutoff a L w → MarkedChain cutoff a H w
  | mark {H L w k} : cutoff ≤ k → VisibleStep a H L k →
      MarkedChain cutoff a L w → MarkedChain cutoff a H (w + k)

def BudgetAtMost (cutoff : ℕ) (a : V) (H : Subgroup (Equiv.Perm V)) (B : ℕ) : Prop :=
  ∀ w, MarkedChain cutoff a H w → w ≤ B

/-- Prefixing an unmarked restriction proves subgroup inheritance at a fixed base point. -/
theorem budget_restrict {cutoff B : ℕ} {a : V}
    {H L : Subgroup (Equiv.Perm V)} (hle : L ≤ H)
    (hB : BudgetAtMost cutoff a H B) : BudgetAtMost cutoff a L B := by
  intro w hw
  exact hB w (.restrict hle hw)

/-- Prefixing a visible quotient pays its entire marked weight. -/
theorem marked_weight_payment {cutoff B k w : ℕ} {a : V}
    {H L : Subgroup (Equiv.Perm V)} (hk : cutoff ≤ k)
    (step : VisibleStep a H L k) (hB : BudgetAtMost cutoff a H B)
    (hw : MarkedChain cutoff a L w) : w + k ≤ B :=
  hB (w + k) (.mark hk step hw)

theorem budget_marked_decrease {cutoff B k : ℕ} {a : V}
    {H L : Subgroup (Equiv.Perm V)} (hk : cutoff ≤ k)
    (step : VisibleStep a H L k) (hB : BudgetAtMost cutoff a H B) :
    k ≤ B ∧ BudgetAtMost cutoff a L (B - k) := by
  have h0 := marked_weight_payment hk step hB (.stop L)
  constructor
  · simpa using h0
  · intro w hw
    have h := marked_weight_payment hk step hB hw
    omega

end GI
