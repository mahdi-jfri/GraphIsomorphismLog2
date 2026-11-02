import Workspace.RadicalSocleStructure

open scoped commutatorElement

namespace GI.PrimitiveStructure

open RadicalSocle

variable {G : Type*} [Group G]

/-- A solvable minimal normal subgroup is abelian. Its characteristic
commutator subgroup cannot be the whole nontrivial solvable group. -/
theorem minimalNormal_solvable_comm {N : Subgroup G}
    (hN : MinimalNormal N) [IsSolvable N] : ∀ x y : N, x * y = y * x := by
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  have hc : commutator N = ⊥ := by
    rcases minimalNormal_characteristic_subgroup hN (commutator N) with hb | ht
    · exact hb
    · have hlt := IsSolvable.commutator_lt_top_of_nontrivial N
      rw [ht] at hlt
      exact (lt_irrefl _ hlt).elim
  intro x y
  have hxy := Subgroup.commutator_mem_commutator
    (Subgroup.mem_top x) (Subgroup.mem_top y)
  change ⁅x, y⁆ ∈ commutator N at hxy
  rw [hc, Subgroup.mem_bot] at hxy
  exact commutatorElement_eq_one_iff_mul_comm.mp hxy

/-- A nontrivial solvable normal subgroup contains a nontrivial abelian
normal subgroup; all normality and solvability transfers are proved. -/
theorem exists_abelian_normal_of_solvable_normal [Finite G]
    (R : Subgroup G) [R.Normal] [IsSolvable R] (hne : R ≠ ⊥) :
    ∃ N : Subgroup G, MinimalNormal N ∧ N ≤ R ∧ ∀ x y : N, x * y = y * x := by
  obtain ⟨N, hN, hNR⟩ := exists_minimal_normal_le R hne
  letI : IsSolvable N := solvable_of_solvable_injective (Subgroup.inclusion_injective hNR)
  exact ⟨N, hN, hNR, minimalNormal_solvable_comm hN⟩

theorem exists_abelian_normal_of_radical_ne_bot [Finite G]
    (hne : solvableRadical G ≠ ⊥) :
    ∃ N : Subgroup G, MinimalNormal N ∧ ∀ x y : N, x * y = y * x := by
  obtain ⟨N, hN, _, hc⟩ := exists_abelian_normal_of_solvable_normal (solvableRadical G) hne
  exact ⟨N, hN, hc⟩

end GI.PrimitiveStructure

#print axioms GI.PrimitiveStructure.minimalNormal_solvable_comm
#print axioms GI.PrimitiveStructure.exists_abelian_normal_of_solvable_normal
#print axioms GI.PrimitiveStructure.exists_abelian_normal_of_radical_ne_bot
