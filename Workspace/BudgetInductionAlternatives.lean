module

public import Workspace.BudgetInductionCore
public import Workspace.BudgetInductionProducts
public import Workspace.BudgetConstants

@[expose] public section

namespace GI.BudgetInduction

/-- The exact outstanding primitive alternatives. The representation data
are actual conjugacies and actual Cartesian/subset actions. The numerical
branch is the order-valuation estimate of A.8. This predicate contains no
marked-chain or sigma assertion. -/
def PrimitiveReductionAlternative (A₀ : ℝ) {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∃ p : ℕ, (p = 3 ∨ p = 5) ∧
    6 * (padicValNat p (Nat.card H) : ℝ) ≤ A₀ * Real.log n) ∨
  (∃ d s : ℕ, 2 ≤ d ∧ 2 ≤ s ∧
    ∃ e : Fin n ≃ (Fin s → Fin d),
      Nonempty (CartesianCover (H.map (relabelPerm e).toMonoidHom))) ∨
  (∃ m t : ℕ, 2 ≤ t ∧ 2 * t ≤ m ∧
    ∃ e : Fin n ≃ Johnson.SubsetVertex (Fin m) t,
      H.map (relabelPerm e).toMonoidHom ≤ Johnson.subsetImage t)

/-- Actual conjugacies and exact cardinal identities discharge all action
adapters in the three displayed primitive branches. -/
theorem sigma_of_primitive_alternative {cutoff n : ℕ} {C A₀ : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C) (hn : 3 ≤ n)
    (absorb : ∀ r : ℕ, 3 ≤ r → A₀ * Real.log r ≤ degreeAllowance C r)
    (ih : ∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    (H : Subgroup (Equiv.Perm (Fin n))) (a : Fin n)
    (alternative : PrimitiveReductionAlternative A₀ H) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C n := by
  rcases alternative with ⟨p, hp, hv⟩ | hc | hj
  · have hs := sigma_valuation_bound hp hcutoff a H
    have hsR : (sigma cutoff a H : ℝ) ≤ 6 * (padicValNat p (Nat.card H) : ℝ) := by
      exact_mod_cast hs
    exact (hsR.trans hv).trans (absorb n hn)
  · obtain ⟨d, s, hd, hs, e, ⟨c⟩⟩ := hc
    have hcard : Fintype.card (Fin s → Fin d) = n := by
      simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
    have h := sigma_cartesian hcutoff hC (by simpa only [hcard] using ih) c (e a)
      (by simpa only [Fintype.card_fin] using hd)
      (by simpa only [Fintype.card_fin] using hs)
    rwa [← sigma_relabel cutoff e H a, hcard] at h
  · obtain ⟨m, t, ht, hhalf, e, hH⟩ := hj
    have hcard : Fintype.card (Johnson.SubsetVertex (Fin m) t) = n := by
      simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
    have h := sigma_johnson hcutoff hC ht hhalf (by simpa only [hcard] using ih)
      _ hH (e a)
    rwa [← sigma_relabel cutoff e H a, hcard] at h

/-- An unconditional minimal-counterexample reduction: a failure of A.9
must occur in a primitive nongiant action outside every proved branch. -/
theorem unsupported_primitive_witness {cutoff : ℕ} {C A₀ : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (absorb : ∀ r : ℕ, 3 ≤ r → A₀ * Real.log r ≤ degreeAllowance C r)
    (failure : ∃ n, ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a ⊤ : ℝ)) :
    ∃ n, cutoff ≤ n ∧ ∃ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) ∧ ¬ alternatingGroup (Fin n) ≤ H ∧
      ¬ PrimitiveReductionAlternative A₀ H ∧
      ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a H : ℝ) := by
  obtain ⟨n, hn, ih, H, hp, hng, a, hfail⟩ :=
    primitive_witness_of_failure hcutoff hC failure
  refine ⟨n, hn, H, hp, hng, ?_, a, hfail⟩
  intro alt
  exact not_lt_of_ge
    (sigma_of_primitive_alternative hcutoff hC (by omega) absorb ih H a alt) hfail

/-- Conditional completion interface, not a completed proof of A.9:
the primitive-exhaustion theorem displayed as `exhaustion` remains to be
proved. All induction, orbit, block and representation adapters are checked. -/
theorem natural_bound_of_primitive_exhaustion {cutoff : ℕ} {C A₀ : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (absorb : ∀ r : ℕ, 3 ≤ r → A₀ * Real.log r ≤ degreeAllowance C r)
    (exhaustion : ∀ n, cutoff ≤ n → ∀ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) → ¬ alternatingGroup (Fin n) ≤ H →
      PrimitiveReductionAlternative A₀ H) :
    ∀ n, ∀ a : Fin n, (sigma cutoff a ⊤ : ℝ) ≤ degreeAllowance C n := by
  apply natural_bound_of_primitive_steps hcutoff hC
  intro n hn ih H hp hng a
  exact sigma_of_primitive_alternative hcutoff hC (by omega) absorb ih H a
    (exhaustion n hn H hp hng)

theorem exists_coefficient_for_primitive_reduction (A₀ : ℝ) (hA : 0 ≤ A₀) :
    ∃ C : ℝ, 128 ≤ C ∧
      ∀ n : ℕ, 3 ≤ n → A₀ * Real.log n ≤ degreeAllowance C n := by
  obtain ⟨C, hC, hh⟩ := exists_budget_coefficient A₀ hA
  refine ⟨C, hC, ?_⟩
  intro n hn
  rw [allowance_large C hn]
  exact hh n (by exact_mod_cast hn)

/-- Uniform hereditary induction, explicitly conditional on the unresolved
primitive exhaustion statement. The coefficient is uniform in every degree
and subgroup; this is an integration theorem, not a claim that exhaustion
or Appendix A.9 has been proved. -/
theorem hereditary_reduction_to_primitive_exhaustion {cutoff : ℕ}
    (hcutoff : 64 ≤ cutoff) (A₀ : ℝ) (hA : 0 ≤ A₀)
    (exhaustion : ∀ n, cutoff ≤ n → ∀ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) → ¬ alternatingGroup (Fin n) ≤ H →
      PrimitiveReductionAlternative A₀ H) :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ n, ∀ H : Subgroup (Equiv.Perm (Fin n)), ∀ a : Fin n,
      (sigma cutoff a H : ℝ) ≤ degreeAllowance C n := by
  obtain ⟨C, hC, absorb⟩ := exists_coefficient_for_primitive_reduction A₀ hA
  have hn := natural_bound_of_primitive_exhaustion hcutoff hC absorb exhaustion
  refine ⟨C, hC, ?_⟩
  intro n H a
  exact (Nat.cast_le.mpr (sigma_subgroup_mono (by omega) a le_top)).trans (hn n a)

end GI.BudgetInduction
