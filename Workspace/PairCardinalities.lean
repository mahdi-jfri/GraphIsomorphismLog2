module

public import Workspace.PairActions
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace GI.Pairs

variable {α : Type*} [Fintype α] [DecidableEq α]

def orderedPairSigma : OrderedPair α ≃ Σ a : α, {b : α // b ≠ a} where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property.symm⟩⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_orderedPair :
    Fintype.card (OrderedPair α) = Fintype.card α * (Fintype.card α - 1) := by
  rw [Fintype.card_congr orderedPairSigma, Fintype.card_sigma]
  have hc : ∀ a : α, Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 := by
    intro a
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp_rw [hc]
  simp

omit [DecidableEq α] in
theorem card_unorderedPair :
    Fintype.card (GI.Johnson.SubsetVertex α 2) = (Fintype.card α).choose 2 :=
  GI.Johnson.card_subsetVertex 2

end GI.Pairs
