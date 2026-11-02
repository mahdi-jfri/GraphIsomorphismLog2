import Workspace.AffineRecognition
namespace GI.AffineRecognition

open MatrixValuation BudgetInduction

variable {V : Type*}
variable (H : Subgroup (Equiv.Perm V)) (N : Subgroup H) [N.Normal] (a : V)
variable (regular : Function.Bijective (fun n : N => n • a))
variable {p d : ℕ} [Fact p.Prime]
variable (basis : N ≃* Multiplicative (Fin d → ZMod p))

/-- An actual permutation group with a regular normal elementary-abelian
subgroup is contained in the constructed physical affine action. -/
theorem permutation_group_le_affine_range :
    H ≤ (physicalAffineAction N a regular basis).range := by
  intro h hh
  refine ⟨affineEmbedding N a regular basis ⟨h, hh⟩, ?_⟩
  exact physicalAffineAction_embedding N a regular basis ⟨h, hh⟩

include N regular basis in
theorem sigma_of_regular_normal_coordinates [Fintype V]
    {cutoff : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) :=
  sigma_affine_image hcutoff hC (physicalAffineAction N a regular basis)
    (degree_eq N a regular basis) H (permutation_group_le_affine_range H N a regular basis) a

/-- The finite degree is derived from the orbit-coordinate bijection;
the affine representation and primitive alternative are conclusions. -/
theorem primitive_alternative_of_regular_normal_coordinates
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (N : Subgroup H) [N.Normal]
    (a : Fin n) (regular : Function.Bijective (fun g : N => g • a))
    {p d : ℕ} [Fact p.Prime] (basis : N ≃* Multiplicative (Fin d → ZMod p))
    {A₀ : ℝ} (hA : 12 / Real.log 2 ≤ A₀) : PrimitiveReductionAlternative A₀ H := by
  apply primitive_alternative_of_affine_image hA
    (physicalAffineAction N a regular basis)
    (by simpa only [Fintype.card_fin] using degree_eq N a regular basis) H
  exact permutation_group_le_affine_range H N a regular basis

end GI.AffineRecognition
