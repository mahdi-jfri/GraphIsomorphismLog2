module

public import Workspace.Proved.GMPOuter
public import Workspace.Proved.GMPNumeric
public import Workspace.PrimitiveUniformCoordinates
public import Workspace.PrimitiveSubdirectDegree

@[expose] public section

/-!
# Counting socle factors using the physical degree

For a minimal normal subgroup, either the point stabilizer has a proper
projection onto a simple factor, or all projections are onto. In the
first case the physical set is a product of coset spaces of size at
least two. In the second case the subgroup order is at most the square
of the degree. The lower bound on the orders of its simple factors
then gives the same power-of-two bound on their count.
-/

namespace GI.Proved

open GI.RadicalSocle GI.PrimitiveStructure GI.PrimitiveCartesian
open GI.Composition

variable {G : Type*} [Group G] [Finite G]

/-- A product of actual nonabelian simple factors has enough order to
pay for sixteen choices per factor. The available lower bound is 34. -/
theorem gmp_sixteen_pow_count_le_card
    (rf : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsoc : socle G = ⊤) :
    16 ^ Nat.card (MinimalNormals G) ≤ Nat.card G := by
  classical
  letI := Fintype.ofFinite (MinimalNormals G)
  have hc : Nat.card G = ∏ N : MinimalNormals G, Nat.card N.val := by
    rw [← Nat.card_congr (GI.RadicalSocle.intrinsicProductEquiv rf hsoc).toEquiv, Nat.card_pi]
  rw [hc, Nat.card_eq_fintype_card]
  calc
    16 ^ Fintype.card (MinimalNormals G) = ∏ _N : MinimalNormals G, 16 := by simp
    _ ≤ ∏ N : MinimalNormals G, Nat.card N.val := by
      apply Finset.prod_le_prod
      intro N _
      have := minimalNormal_simple_of_socle_eq_top hsoc N.property
      exact (by decide : 16 ≤ 34).trans
        (GI.SmallSimple.thirtyfour_le_card (by
          obtain ⟨x, y, hxy⟩ := minimalNormal_nonabelian rf N.property
          exact fun hc => hxy (hc x y)))

/-- The simple-factor count of a nonabelian primitive minimal normal
subgroup is at most the base-two logarithm of the action degree. -/
theorem gmp_minimalNormal_count_degree {V : Type*} [MulAction G V]
    [FaithfulSMul G V] [Nontrivial V] [MulAction.IsPreprimitive G V]
    (rf : ∀ K : Subgroup G, K.Normal → Group.IsSolvable K → K = ⊥)
    (N : Subgroup G) [N.Normal] (hN : MinimalNormal N) (a : V) :
    2 ^ Nat.card (MinimalNormals N) ≤ Nat.card V := by
  classical
  have := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  obtain ⟨K, hK, _⟩ := exists_minimal_normal_le (⊤ : Subgroup N) top_ne_bot
  let i : MinimalNormals N := ⟨K, hK⟩
  by_cases hproper : ∃ j : MinimalNormals N,
      ((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding rf N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j) ≠ ⊤
  · obtain ⟨j, hj⟩ := hproper
    rw [primitive_uniform_degree rf N hN a j hj]
    exact Nat.pow_le_pow_left (Subgroup.one_lt_index_of_ne_top hj) _
  · have honto : ∀ j : MinimalNormals N,
        ((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding rf N hN)).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j) = ⊤ := by
      intro j
      by_contra hj
      exact hproper ⟨j, hj⟩
    have horder := minimalNormal_card_le_degree_sq_of_subdirect rf N hN a i honto
    have hlow := gmp_sixteen_pow_count_le_card
      (normal_subgroup_radicalFree rf N) (minimalNormal_socle_eq_top hN)
    have hsquare : (2 ^ Nat.card (MinimalNormals N)) ^ 2 ≤ Nat.card V ^ 2 := by
      calc
        (2 ^ Nat.card (MinimalNormals N)) ^ 2 = 4 ^ Nat.card (MinimalNormals N) := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
        _ ≤ 16 ^ Nat.card (MinimalNormals N) := Nat.pow_le_pow_left (by decide) _
        _ ≤ Nat.card V ^ 2 := hlow.trans horder
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare

end GI.Proved
