import Workspace.AffineRecognitionBudget
import Workspace.PrimitiveAbelianCoordinates
namespace GI.AffineRecognition

open BudgetInduction PrimitiveStructure

/-- A nontrivial abelian normal subgroup of an actual finite primitive
permutation group gives the proved affine valuation alternative. Regularity,
prime exponent, vector-space coordinates, and the affine action are all
derived in the imported proofs. -/
theorem primitive_alternative_of_abelian_normal
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive H (Fin n)]
    (N : Subgroup H) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : Fin n)
    {A₀ : ℝ} (hA : 12 / Real.log 2 ≤ A₀) : PrimitiveReductionAlternative A₀ H := by
  obtain ⟨p, hp, d, ⟨basis⟩⟩ := abelian_normal_coordinates N hne comm a
  letI : Fact p.Prime := ⟨hp⟩
  exact primitive_alternative_of_regular_normal_coordinates H N a
    (abelian_normal_regular N hne comm a) basis hA

/-- The actual hereditary-budget bound for a primitive group with a
nontrivial abelian normal subgroup. No affine representation is supplied
as an input assumption. -/
theorem sigma_of_abelian_normal {V : Type*} [Fintype V]
    (H : Subgroup (Equiv.Perm V)) [MulAction.IsPreprimitive H V]
    (N : Subgroup H) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V)
    {cutoff : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  obtain ⟨p, hp, d, ⟨basis⟩⟩ := abelian_normal_coordinates N hne comm a
  letI : Fact p.Prime := ⟨hp⟩
  exact sigma_of_regular_normal_coordinates H N a
    (abelian_normal_regular N hne comm a) basis hcutoff hC

end GI.AffineRecognition
