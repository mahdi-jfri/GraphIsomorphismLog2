module

public import Workspace.PrimitiveCentralizer
public import Workspace.RadicalSocleProduct

@[expose] public section

namespace GI.PrimitiveStructure

open RadicalSocle

variable {G V : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]
variable [MulAction.IsPreprimitive G V]

/-- Distinct minimal normal subgroups of a faithful primitive group each
act regularly on the original point set. -/
theorem distinct_minimal_normals_regular {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    Function.Bijective (fun m : M => m • a) ∧
      Function.Bijective (fun n : N => n • a) := by
  letI := hM.1
  letI := hN.1
  letI := normal_pretransitive (V := V) M hM.2.1
  letI := normal_pretransitive (V := V) N hN.2.1
  exact ⟨commuting_transitive_regular M N (minimalNormal_commute hM hN hne) a,
    commuting_transitive_regular N M (minimalNormal_commute hN hM hne.symm) a⟩

theorem distinct_minimal_normals_centralizers {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    Subgroup.centralizer (N : Set G) = M ∧ Subgroup.centralizer (M : Set G) = N := by
  letI := hM.1
  letI := hN.1
  letI := normal_pretransitive (V := V) M hM.2.1
  letI := normal_pretransitive (V := V) N hN.2.1
  exact ⟨centralizer_eq_of_commuting_transitive M N (minimalNormal_commute hM hN hne) a,
    centralizer_eq_of_commuting_transitive N M (minimalNormal_commute hN hM hne.symm) a⟩

/-- Once two distinct minimal normal subgroups are present, every actual
minimal normal subgroup equals one of them. -/
theorem minimalNormal_eq_one_of_pair {M N K : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N)
    (hK : MinimalNormal K) (a : V) : K = M ∨ K = N := by
  by_cases hKM : K = M
  · exact Or.inl hKM
  · right
    have hKN : K ≤ N := by
      rw [← (distinct_minimal_normals_centralizers hM hN hne a).2]
      intro k hk m hm
      exact (minimalNormal_commute hK hM hKM ⟨k, hk⟩ ⟨m, hm⟩).symm
    exact (hN.2.2 K hK.1 hKN).resolve_left hK.2.1

/-- The degree equals the order of each regular minimal normal subgroup. -/
theorem distinct_minimal_normals_card_degree {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    Nat.card M = Nat.card V ∧ Nat.card N = Nat.card V := by
  obtain ⟨hregM, hregN⟩ := distinct_minimal_normals_regular hM hN hne a
  exact ⟨Nat.card_congr (Equiv.ofBijective _ hregM),
    Nat.card_congr (Equiv.ofBijective _ hregN)⟩

theorem minimalNormal_card_le_two [Finite G] (a : V) : Nat.card (MinimalNormals G) ≤ 2 := by
  classical
  letI := Fintype.ofFinite (MinimalNormals G)
  by_cases hpair : ∃ M N : MinimalNormals G, M ≠ N
  · obtain ⟨M, N, hne⟩ := hpair
    have hsub : (Finset.univ : Finset (MinimalNormals G)) ⊆ {M, N} := by
      intro K _
      rcases minimalNormal_eq_one_of_pair M.property N.property
        (fun h => hne (Subtype.ext h)) K.property a with hm | hn
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Subtype.ext hm)
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Subtype.ext hn)
    have hcard := Finset.card_le_card hsub
    simpa only [Finset.card_univ, Finset.card_pair hne, Nat.card_eq_fintype_card] using hcard
  · haveI : Subsingleton (MinimalNormals G) :=
      ⟨fun M N => not_ne_iff.mp (fun hne => hpair ⟨M, N, hne⟩)⟩
    have hcard := Finset.card_le_one_of_subsingleton (Finset.univ : Finset (MinimalNormals G))
    rw [Finset.card_univ] at hcard
    rw [Nat.card_eq_fintype_card]
    omega

theorem socle_eq_sup_of_distinct_minimal_normals {M N : Subgroup G}
    (hM : MinimalNormal M) (hN : MinimalNormal N) (hne : M ≠ N) (a : V) :
    socle G = M ⊔ N := by
  letI := hM.1
  letI := hN.1
  apply le_antisymm
  · apply socle_le_normal
    intro K hK
    rcases minimalNormal_eq_one_of_pair hM hN hne hK a with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (minimalNormal_le_socle hM) (minimalNormal_le_socle hN)

end GI.PrimitiveStructure
