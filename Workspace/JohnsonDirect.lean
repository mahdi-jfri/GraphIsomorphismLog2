import Workspace.JohnsonChains
import Workspace.SmallDegreeBudget

namespace GI.Johnson.JohnsonCover

variable {V α : Type*} [DecidableEq α] {H L : Subgroup (Equiv.Perm V)}

/-- Faithfulness of the subset labeling lets every original quotient descend
to the natural image, even when its kernel is not naturally transitive. -/
noncomputable def directStep (c : JohnsonCover H α) {a : V} {k : ℕ}
    (s : VisibleStep a H L k) :
    AlternatingQuotientStep c.project.range (c.restrict s.lower).project.range k := by
  have hk : c.project.ker ≤ s.quotient.ker := by
    intro h hh
    have hh1 : h = 1 := c.project_injective (hh.trans (map_one c.project).symm)
    change s.quotient h = 1
    rw [hh1, map_one]
  have step := QuotientImage.step c.project s.quotient s.quotient.ker s.onto (fun _ => Iff.rfl) hk
  rwa [c.natural_kernel_range s] at step

theorem directChain {cutoff w : ℕ} {a : V} (chain : MarkedChain cutoff a H w)
    (c : JohnsonCover H α) : QuotientChain cutoff c.project.range w := by
  induction chain with
  | stop H => exact .stop _
  | restrict hle _ ih => exact .restrict (c.restrict_range_le hle) (ih (c.restrict hle))
  | mark hk s _ ih => exact .mark hk (c.directStep s) (ih (c.restrict s.lower))

theorem direct_chain_bound [Fintype α] {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff)
    {a : V} (chain : MarkedChain cutoff a H w) (c : JohnsonCover H α) :
    w ≤ 3 * (Fintype.card α - 1) :=
  quotient_chain_permutation_card_bound hcutoff (c.directChain chain)

theorem chain_zero_of_degree [Fintype α] {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (hdegree : Fintype.card α < cutoff) {a : V}
    (chain : MarkedChain cutoff a H w) (c : JohnsonCover H α) : w = 0 :=
  quotient_chain_zero_of_card hcutoff hdegree (c.directChain chain)
    (permutation_subgroup_card_le_factorial c.project.range)

end GI.Johnson.JohnsonCover
