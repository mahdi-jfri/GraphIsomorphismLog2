import Workspace.BudgetInductionAlternatives
import Mathlib.GroupTheory.Solvable

namespace GI

/-- Solvable groups have no nonabelian alternating quotient. -/
theorem no_alternating_surjection_of_solvable {G : Type*} [Group G] [IsSolvable G]
    {k : ℕ} (hk : 5 ≤ k) (q : G →* alternatingGroup (Fin k)) :
    ¬ Function.Surjective q := by
  intro onto
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  haveI : IsSolvable (alternatingGroup (Fin k)) := solvable_of_surjective onto
  obtain ⟨f, g, hfg⟩ := AlternatingSimple.nonabelian_fin hk
  exact hfg (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance f g)

/-- Restriction to an actual subgroup preserves solvability. -/
theorem solvable_of_subgroup_le {G : Type*} [Group G]
    {H L : Subgroup G} (hle : L ≤ H) [IsSolvable H] : IsSolvable L :=
  solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

/-- Every alternating quotient chain in a solvable group has zero weight,
including chains which repeatedly restrict to arbitrary subgroups. -/
theorem quotient_chain_zero_of_solvable {G : Type*} [Group G]
    {H : Subgroup G} {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (chain : QuotientChain cutoff H w) : IsSolvable H → w = 0 := by
  induction chain with
  | stop H => intro _; rfl
  | restrict hle _ ih =>
    intro hs
    letI := hs
    exact ih (solvable_of_subgroup_le hle)
  | mark hk step _ _ =>
    intro hs
    letI := hs
    exact (no_alternating_surjection_of_solvable (hcutoff.trans hk)
      step.quotient step.onto).elim

theorem marked_chain_zero_of_solvable {V : Type*} {a : V}
    {H : Subgroup (Equiv.Perm V)} {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (chain : MarkedChain cutoff a H w) [IsSolvable H] : w = 0 :=
  quotient_chain_zero_of_solvable hcutoff chain.toQuotientChain inferInstance

/-- This bound applies to every solvable permutation group, without
primitive-action recognition or a supplied affine representation. -/
theorem sigma_zero_of_solvable {V : Type*} [Fintype V]
    {H : Subgroup (Equiv.Perm V)} {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (a : V) [IsSolvable H] : sigma cutoff a H = 0 :=
  marked_chain_zero_of_solvable hcutoff (sigma_achieved hcutoff a H)

namespace BudgetInduction

/-- An unsupported primitive counterexample must also be nonsolvable.
This is an unconditional reduction and does not assert primitive exhaustion. -/
theorem unsupported_nonsolvable_primitive_witness {cutoff : ℕ} {C A₀ : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (absorb : ∀ r : ℕ, 3 ≤ r → A₀ * Real.log r ≤ degreeAllowance C r)
    (failure : ∃ n, ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a ⊤ : ℝ)) :
    ∃ n, cutoff ≤ n ∧ ∃ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) ∧ ¬ alternatingGroup (Fin n) ≤ H ∧
      ¬ IsSolvable H ∧ ¬ PrimitiveReductionAlternative A₀ H ∧
      ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a H : ℝ) := by
  obtain ⟨n, hn, H, hp, hng, halt, a, hfail⟩ :=
    unsupported_primitive_witness hcutoff hC absorb failure
  refine ⟨n, hn, H, hp, hng, ?_, halt, a, hfail⟩
  intro hs
  letI := hs
  have hz := sigma_zero_of_solvable (by omega : 5 ≤ cutoff) a (H := H)
  rw [hz, Nat.cast_zero] at hfail
  exact not_lt_of_ge (allowance_nonneg hC n) hfail

end BudgetInduction
end GI

#print axioms GI.no_alternating_surjection_of_solvable
#print axioms GI.solvable_of_subgroup_le
#print axioms GI.quotient_chain_zero_of_solvable
#print axioms GI.marked_chain_zero_of_solvable
#print axioms GI.sigma_zero_of_solvable
#print axioms GI.BudgetInduction.unsupported_nonsolvable_primitive_witness
