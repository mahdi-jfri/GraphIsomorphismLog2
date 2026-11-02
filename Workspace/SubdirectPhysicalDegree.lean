import Workspace.SubdirectCardBound
import Workspace.FaithfulProductStabilizer

namespace GI.PrimitiveProducts

variable {S I V : Type*} [Group S] [DecidableEq I]

/-- For an actual faithful transitive product action with subdirect point
stabilizer, the actual product order is at most the square of its physical
degree. No diagonal-action representation is assumed. -/
theorem subdirect_action_card_le_degree_sq [Finite S] [IsSimpleGroup S] [Fintype I]
    [MulAction (I → S) V] [FaithfulSMul (I → S) V]
    [MulAction.IsPretransitive (I → S) V]
    (nonabelian : ∃ x y : S, x * y ≠ y * x) (a : V)
    (hsub : Subdirect (MulAction.stabilizer (I → S) a)) :
    Nat.card (I → S) ≤ Nat.card V ^ 2 := by
  have h := subdirect_ambient_card_le_index_sq nonabelian (MulAction.stabilizer (I → S) a)
    hsub (stabilizer_noFullFactors a)
  rwa [MulAction.index_stabilizer_of_transitive] at h

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.subdirect_action_card_le_degree_sq
