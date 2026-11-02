import Workspace.PrimitiveRegularSocle
import Workspace.PrimitiveSolvableNormal
import Workspace.RadicalSocleHomogeneous

namespace GI.PrimitiveStructure

open RadicalSocle

variable {G V : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]
variable [MulAction.IsPreprimitive G V]

/-- Two distinct minimal normal subgroups force each to be nonabelian:
an abelian regular group already equals its own centralizer. -/
theorem minimalNormal_nonabelian_of_pair {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    ∃ x y : M, x * y ≠ y * x := by
  classical
  by_contra hab
  push Not at hab
  letI := hM.1
  letI := normal_pretransitive (V := V) M hM.2.1
  have hcM := centralizer_eq_of_commuting_transitive M M
    (fun x y => congrArg Subtype.val (hab x y)) a
  have hcN := (distinct_minimal_normals_centralizers hM hN hne a).2
  exact hne (hcM.symm.trans hcN)

/-- No solvable normal subgroup survives in a finite faithful primitive
group with two distinct minimal normal subgroups. -/
theorem two_minimal_radical_free [Finite G] {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    ∀ R : Subgroup G, R.Normal → IsSolvable R → R = ⊥ := by
  intro R hR hsolv
  by_contra hRne
  letI := hR
  letI := hsolv
  obtain ⟨K, hK, _, comm⟩ := exists_abelian_normal_of_solvable_normal R hRne
  rcases minimalNormal_eq_one_of_pair hM hN hne hK a with rfl | rfl
  · obtain ⟨x, y, hxy⟩ := minimalNormal_nonabelian_of_pair hM hN hne a
    exact hxy (comm x y)
  · obtain ⟨x, y, hxy⟩ := minimalNormal_nonabelian_of_pair hN hM hne.symm a
    exact hxy (comm x y)

/-- For two regular minimal normal subgroups, the physical degree and
the order of the full socle are explicit powers of an actual finite
nonabelian simple factor. This is the exact two-normal degree case. -/
theorem two_minimal_degree_simple_power [Finite G] {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    ∃ K : MinimalNormals M, IsSimpleGroup K.val ∧
      (∃ x y : K.val, x * y ≠ y * x) ∧
      Nat.card V = Nat.card K.val ^ Nat.card (MinimalNormals M) ∧
      Nat.card (socle G) = Nat.card K.val ^ (2 * Nat.card (MinimalNormals M)) := by
  have radicalFree := two_minimal_radical_free hM hN hne a
  obtain ⟨K, hs, hab, _⟩ := minimalNormal_exists_simple_power radicalFree hM
  have hd : Nat.card V = Nat.card K.val ^ Nat.card (MinimalNormals M) :=
    (distinct_minimal_normals_card_degree hM hN hne a).1.symm.trans
      (minimalNormal_card_power radicalFree hM K)
  refine ⟨K, hs, hab, hd, ?_⟩
  rw [two_minimal_socle_card_eq_degree_sq hM hN hne a, hd, ← pow_mul, Nat.mul_comm]

end GI.PrimitiveStructure

#print axioms GI.PrimitiveStructure.minimalNormal_nonabelian_of_pair
#print axioms GI.PrimitiveStructure.two_minimal_radical_free
#print axioms GI.PrimitiveStructure.two_minimal_degree_simple_power
