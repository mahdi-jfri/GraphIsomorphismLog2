module

public import Workspace.CartesianStep
public import Workspace.AlternatingSimple
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

open scoped BigOperators

namespace GI.CartesianCover

variable {I D : Type*} [Fintype I] [Fintype D]
variable {H : Subgroup (Equiv.Perm (I → D))}

/-- An entire physical marked chain splits into one position quotient chain
and one actual marked chain for each fixed component. -/
theorem chain_split {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff) {v : I → D}
    (hw : MarkedChain cutoff v H w) :
    ∀ c : CartesianCover H, ∃ r : ℕ, ∃ weights : I → ℕ,
      r + ∑ i, weights i = w ∧ QuotientChain cutoff (c.rowProject v).range r ∧
      ∀ i : I, MarkedChain cutoff (v i) (c.component i).range (weights i) := by
  classical
  induction hw with
  | stop H =>
      intro c
      exact ⟨0, fun _ => 0, by simp, .stop _, fun _ => .stop _⟩
  | restrict hle _ ih =>
      intro c
      obtain ⟨r, weights, heq, hr, hs⟩ := ih (c.restrict hle)
      exact ⟨r, weights, heq, .restrict (c.restrict_row_range_le hle v) hr,
        fun i => .restrict (c.restrict_component_range_le hle i) (hs i)⟩
  | @mark H L w k hk s _ ih =>
      intro c
      obtain ⟨r, weights, heq, hr, hs⟩ := ih (c.restrict s.lower)
      letI := AlternatingSimple.isSimple_fin (hcutoff.trans hk)
      have nonabelian := AlternatingSimple.nonabelian_fin (hcutoff.trans hk)
      rcases c.visible_step_split nonabelian s with hrow | hcomponent
      · obtain ⟨sr⟩ := hrow
        exact ⟨r + k, weights, by omega, .mark hk sr hr,
          fun i => .restrict (c.restrict_component_range_le s.lower i) (hs i)⟩
      · obtain ⟨i, si⟩ := hcomponent
        obtain ⟨si⟩ := si
        let weights' : I → ℕ := fun j => weights j + if j = i then k else 0
        have hsum : ∑ j, weights' j = (∑ j, weights j) + k := by
          simp only [weights', Finset.sum_add_distrib]
          simp
        refine ⟨r, weights', by omega, .restrict (c.restrict_row_range_le s.lower v) hr, ?_⟩
        intro j
        by_cases hj : j = i
        · subst j
          change MarkedChain cutoff (v i) (c.component i).range
            (weights i + if i = i then k else 0)
          rw [if_pos rfl]
          exact .mark hk si (hs i)
        · have hwj : weights' j = weights j := by simp [weights', hj]
          rw [hwj]
          exact .restrict (c.restrict_component_range_le s.lower j) (hs j)

theorem budget_cartesian {cutoff : ℕ} (hcutoff : 64 ≤ cutoff)
    (c : CartesianCover H) (v : I → D) (budgets : I → ℕ)
    (hbudgets : ∀ i : I, BudgetAtMost cutoff (v i) (c.component i).range (budgets i)) :
    BudgetAtMost cutoff v H (3 * (Fintype.card I - 1) + ∑ i, budgets i) := by
  intro w hw
  have hfive : 5 ≤ cutoff := by omega
  obtain ⟨r, weights, heq, hr, hs⟩ := chain_split hfive hw c
  have hrbound := quotient_chain_permutation_card_bound hcutoff hr
  have hsum : ∑ i, weights i ≤ ∑ i, budgets i := by
    apply Finset.sum_le_sum
    intro i _
    exact hbudgets i (weights i) (hs i)
  omega

/-- Lemma A.6, with actual arbitrary active orbits and no independence
assumption on the coordinate projections. -/
theorem sigma_cartesian_le [Fintype (I → D)] {cutoff : ℕ} (hcutoff : 64 ≤ cutoff)
    (c : CartesianCover H) (v : I → D) :
    sigma cutoff v H ≤ 3 * (Fintype.card I - 1) +
      ∑ i, sigma cutoff (v i) (c.component i).range := by
  have hfive : 5 ≤ cutoff := by omega
  obtain ⟨r, weights, heq, hr, hs⟩ := chain_split hfive (sigma_achieved hfive v H) c
  have hrbound := quotient_chain_permutation_card_bound hcutoff hr
  have hsum : ∑ i, weights i ≤ ∑ i, sigma cutoff (v i) (c.component i).range := by
    apply Finset.sum_le_sum
    intro i _
    exact sigma_bounds_chain hfive (hs i)
  omega

end GI.CartesianCover
