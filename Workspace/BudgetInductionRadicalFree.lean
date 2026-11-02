import Workspace.AffineRecognitionPrimitive
import Workspace.PrimitiveSolvableNormal
namespace GI.BudgetInduction

open RadicalSocle PrimitiveStructure

/-- The affine alternative follows from a nontrivial solvable radical in
an actual primitive permutation group. The abelian normal subgroup,
prime-field coordinates and affine representation are all constructed. -/
theorem primitive_alternative_of_nontrivial_solvable_radical
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive H (Fin n)] (a : Fin n)
    (hne : solvableRadical H ≠ ⊥) {A₀ : ℝ} (hA : 12 / Real.log 2 ≤ A₀) :
    PrimitiveReductionAlternative A₀ H := by
  obtain ⟨N, hN, comm⟩ := exists_abelian_normal_of_radical_ne_bot hne
  letI := hN.1
  exact AffineRecognition.primitive_alternative_of_abelian_normal H N hN.2.1 comm a hA

/-- The same actual construction bounds every primitive action with a
nontrivial solvable normal subgroup, without assuming an affine model. -/
theorem sigma_primitive_of_nontrivial_solvable_normal
    {V : Type*} [Fintype V] (H : Subgroup (Equiv.Perm V))
    [MulAction.IsPreprimitive H V] (R : Subgroup H) [R.Normal] [IsSolvable R]
    (hne : R ≠ ⊥) (a : V) {cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  obtain ⟨N, hN, _, comm⟩ := exists_abelian_normal_of_solvable_normal R hne
  letI := hN.1
  exact AffineRecognition.sigma_of_abelian_normal H N hN.2.1 comm a hcutoff hC

/-- A failed natural bound has a primitive nongiant witness outside all
proved alternatives and with trivial solvable radical. This is a genuine
reduction, not a claim that the remaining primitive cases are exhausted. -/
theorem unsupported_radical_free_primitive_witness {cutoff : ℕ} {C A₀ : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C)
    (absorb : ∀ r : ℕ, 3 ≤ r → A₀ * Real.log r ≤ degreeAllowance C r)
    (failure : ∃ n, ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a ⊤ : ℝ)) :
    ∃ n, cutoff ≤ n ∧ ∃ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) ∧ ¬ alternatingGroup (Fin n) ≤ H ∧
      solvableRadical H = ⊥ ∧ ¬ PrimitiveReductionAlternative A₀ H ∧
      ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a H : ℝ) := by
  obtain ⟨n, hn, H, hp, hng, halt, a, hfail⟩ :=
    unsupported_primitive_witness hcutoff (by linarith) absorb failure
  letI := hp
  refine ⟨n, hn, H, hp, hng, ?_, halt, a, hfail⟩
  by_contra hrad
  have hb := sigma_primitive_of_nontrivial_solvable_normal H (solvableRadical H)
    hrad a hcutoff hC
  rw [Fintype.card_fin] at hb
  exact not_lt_of_ge hb hfail

end GI.BudgetInduction

#print axioms GI.BudgetInduction.primitive_alternative_of_nontrivial_solvable_radical
#print axioms GI.BudgetInduction.sigma_primitive_of_nontrivial_solvable_normal
#print axioms GI.BudgetInduction.unsupported_radical_free_primitive_witness
