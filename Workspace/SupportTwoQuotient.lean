import Workspace.PairComplement
import Workspace.StabilizerImage

namespace GI.Pairs

open Equiv Equiv.Perm

variable {α G V : Type*} [Fintype α] [DecidableEq α] [Group G] [MulAction G V]

/-- The mathematical quotient assertion of A.26, directly from IR1. The
quotient map, its surjectivity, equivariance, exact kernel fibers, and equal
fiber sizes are constructed. This theorem makes no polynomial-time claim. -/
theorem support_two_quotient (h4 : 4 ≤ Fintype.card α)
    (φ : G →* alternatingGroup α) (onto : Function.Surjective φ)
    (x : V) (transitive : ∀ y : V, ∃ g : G, g • x = y)
    (a b : α) (hab : a ≠ b)
    (lower : (GI.AlternatingSimple.extend (complementLabels a b)).range ≤
      (MulAction.stabilizer G x).map φ)
    (upper : (MulAction.stabilizer G x).map φ ≤ setwise a b hab) :
    Nonempty (StabilizerQuotient.KernelQuotient φ V (OrderedPair α)) ∨
      Nonempty (StabilizerQuotient.KernelQuotient φ V (GI.Johnson.SubsetVertex α 2)) := by
  rcases support_two_stabilizer_dichotomy a b hab _ lower upper with ho | hu
  · left
    exact ⟨StabilizerQuotient.kernelQuotientOfImage φ x (⟨(a, b), hab⟩ : OrderedPair α)
      onto transitive (ordered_transitive h4 _) ho⟩
  · right
    exact ⟨StabilizerQuotient.kernelQuotientOfImage φ x (unorderedOfOrdered ⟨(a, b), hab⟩)
      onto transitive (unordered_transitive h4 _) hu⟩

end GI.Pairs
