import Workspace.BlockChain
import Workspace.AlternatingSimple

namespace GI.BlockCover

variable {V B : Type*} [Fintype V]
variable {H : Subgroup (Equiv.Perm V)}

/-- The two actual projected chains account for every marked weight, including
marks after arbitrary subgroup and active-orbit restrictions. -/
theorem chain_split {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff) {a : V}
    (hw : MarkedChain cutoff a H w) (c : BlockCover H B) :
    ∃ u v : ℕ, u + v = w ∧
      MarkedChain cutoff (c.label a) c.project.range u ∧
      MarkedChain cutoff (c.localBase a) (c.localProject a).range v :=
  chain_split_of_simple
    (fun _ hk => AlternatingSimple.isSimple_fin (hcutoff.trans hk))
    (fun _ hk => AlternatingSimple.nonabelian_fin (hcutoff.trans hk)) hw c

theorem budget_block {cutoff topBudget localBudget : ℕ} (hcutoff : 5 ≤ cutoff)
    (c : BlockCover H B) (a : V)
    (htop : BudgetAtMost cutoff (c.label a) c.project.range topBudget)
    (hlocal : BudgetAtMost cutoff (c.localBase a) (c.localProject a).range localBudget) :
    BudgetAtMost cutoff a H (topBudget + localBudget) := by
  intro w hw
  obtain ⟨u, v, huv, hu, hv⟩ := chain_split hcutoff hw c
  have hu' := htop u hu
  have hv' := hlocal v hv
  omega

/-- Lemma A.5, hereditary block decomposition, for the actual marked-chain
maximum and the actual top and block-stabilizer permutation images.

An equivariant block labeling supplies the block system. The theorem in fact
holds without assuming transitivity of the initial action or equal block sizes.
There are no unproved localization or chain-transfer hypotheses. -/
theorem sigma_block_le [Fintype B] {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (c : BlockCover H B) (a : V)
    [Fintype {x : V // c.label x = c.label a}] :
    sigma cutoff a H ≤ sigma cutoff (c.label a) c.project.range +
      sigma cutoff (c.localBase a) (c.localProject a).range :=
  sigma_block_le_of_simple hcutoff
    (fun _ hk => AlternatingSimple.isSimple_fin (hcutoff.trans hk))
    (fun _ hk => AlternatingSimple.nonabelian_fin (hcutoff.trans hk)) c a

end GI.BlockCover
