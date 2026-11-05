module

public import Workspace.Proved.GMPDegree
public import Workspace.Proved.GMPAffine
public import Workspace.PrimitiveTwoNormalDegree
public import Workspace.PrimitiveSolvableNormal

@[expose] public section

/-! # The primitive case of GMP, Theorem 5.1 -/

namespace GI.Proved

open GI.Composition GI.RadicalSocle GI.RadicalFreeOrder GI.PrimitiveStructure

variable {G V : Type*} [Group G] [Finite G] [MulAction G V]
  [FaithfulSMul G V] [MulAction.IsPreprimitive G V]

/-- Two distinct minimal normal subgroups leave room in the degree
bound for both the inner quotient and the permutation of simple factors. -/
theorem gmp_two_minimal_count_degree [Nontrivial G]
    {M N : Subgroup G} (hM : MinimalNormal M) (hN : MinimalNormal N)
    (hne : M ≠ N) (a : V) :
    2 ^ (Nat.card (MinimalNormals (socle G)) + 1) ≤ Nat.card V := by
  have rf := two_minimal_radical_free hM hN hne a
  have hlow := gmp_sixteen_pow_count_le_card
    (normal_subgroup_radicalFree rf (socle G)) socle_idempotent
  rw [two_minimal_socle_card_eq_degree_sq hM hN hne a] at hlow
  have hsquare : (4 ^ Nat.card (MinimalNormals (socle G))) ^ 2 ≤ Nat.card V ^ 2 := by
    calc
      (4 ^ Nat.card (MinimalNormals (socle G))) ^ 2 =
          16 ^ Nat.card (MinimalNormals (socle G)) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
      _ ≤ _ := hlow
  have hfour := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare
  have hpos := nontrivial_factors (G := G)
  calc
    2 ^ (Nat.card (MinimalNormals (socle G)) + 1) ≤
        2 ^ (2 * Nat.card (MinimalNormals (socle G))) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ Nat.card (MinimalNormals (socle G)) := by rw [pow_mul]; rfl
    _ ≤ _ := hfour

/-- In the two-minimal-normal case, quotienting by either minimal normal
subgroup leaves exactly one degree's worth of socle order. -/
theorem gmp_two_minimal_socle_quotient_card [Finite V]
    {M N : Subgroup G} [M.Normal] (hM : MinimalNormal M) (hN : MinimalNormal N)
    (hne : M ≠ N) (a : V) :
    Nat.card (socle G ⧸ M.subgroupOf (socle G)) = Nat.card V := by
  have hle := minimalNormal_le_socle hM
  have h := (M.subgroupOf (socle G)).card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    (distinct_minimal_normals_card_degree hM hN hne a).1,
    two_minimal_socle_card_eq_degree_sq hM hN hne a, pow_two] at h
  have : Nonempty V := ⟨a⟩
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

/-- The nonabelian primitive case, for every nontrivial normal kernel. -/
theorem gmp_radicalFree_primitive_quotient_bound {n : ℕ} (hn : 2 ≤ n)
    (A : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive A (Fin n)]
    (rf : ∀ K : Subgroup A, K.Normal → Group.IsSolvable K → K = ⊥)
    (R : Subgroup A) [R.Normal] (hR : R ≠ ⊥) :
    (bFac (A ⧸ R) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let a : Fin n := ⟨0, by omega⟩
  obtain ⟨M, hM, hMR⟩ := exists_minimal_normal_le R hR
  have : M.Normal := hM.1
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM.2.1
  obtain ⟨g, hg, hgne⟩ := M.exists_ne_one_of_nontrivial
  have : Nontrivial A := ⟨⟨g, 1, hgne⟩⟩
  have hquot := gmp_bFac_quotient_antitone M R hMR
  by_cases hpair : ∃ N : Subgroup A, MinimalNormal N ∧ M ≠ N
  · obtain ⟨N, hN, hne⟩ := hpair
    have : N.Normal := hN.1
    have hchain := gmp_bFac_quotient_chain M (socle A) (minimalNormal_le_socle hM)
    have hcard : Nat.card (socle A ⧸ M.subgroupOf (socle A)) = n := by
      simpa only [Nat.card_fin] using gmp_two_minimal_socle_quotient_card hM hN hne a
    have hnat : bFac (A ⧸ R) ≤ n * (Nat.card (MinimalNormals (socle A))).factorial := by
      apply hquot.trans
      rw [hchain]
      exact Nat.mul_le_mul (bFac_le_card.trans_eq hcard)
        (gmp_bFac_quotient_socle_le_factorial rf)
    have hdeg : 2 ^ (Nat.card (MinimalNormals (socle A)) + 1) ≤ n := by
      simpa only [Nat.card_fin] using gmp_two_minimal_count_degree hM hN hne a
    have hbound := gmp_factorial_degree_bound (by omega : 1 ≤ n) hdeg
    norm_num only [pow_one] at hbound
    exact (show (bFac (A ⧸ R) : ℝ) ≤ _ by exact_mod_cast hnat).trans hbound
  · have hsoc : socle A = M := by
      apply le_antisymm
      · apply socle_le_normal
        intro N hN
        exact le_of_eq (not_ne_iff.mp (fun hne => hpair ⟨N, hN, hne.symm⟩))
      · exact minimalNormal_le_socle hM
    have hnat : bFac (A ⧸ R) ≤ (Nat.card (MinimalNormals M)).factorial := by
      apply hquot.trans
      have h := gmp_bFac_quotient_socle_le_factorial rf
      let e : A ⧸ socle A ≃* A ⧸ M :=
        QuotientGroup.congr _ _ (MulEquiv.refl A) (by simpa using hsoc)
      have hc : Nat.card (MinimalNormals (socle A)) = Nat.card (MinimalNormals M) := by
        rw [hsoc]
      rw [bFac_congr e, hc] at h
      exact h
    have hdeg : 2 ^ Nat.card (MinimalNormals M) ≤ n := by
      simpa only [Nat.card_fin] using gmp_minimalNormal_count_degree rf M hM a
    have hbound := gmp_factorial_degree_bound (d := 0) (by omega : 1 ≤ n)
      (by simpa only [Nat.add_zero] using hdeg)
    norm_num only [pow_zero, one_mul] at hbound
    exact (show (bFac (A ⧸ R) : ℝ) ≤ _ by exact_mod_cast hnat).trans hbound

/-- The complete primitive case of GMP, Theorem 5.1. -/
theorem gmp_primitive_quotient_bound {n : ℕ} (hn : 2 ≤ n)
    (A : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive A (Fin n)]
    (R : Subgroup A) [R.Normal] (hR : R ≠ ⊥) :
    (bFac (A ⧸ R) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  classical
  by_cases rf : ∀ K : Subgroup A, K.Normal → Group.IsSolvable K → K = ⊥
  · exact gmp_radicalFree_primitive_quotient_bound hn A rf R hR
  · push Not at rf
    obtain ⟨K, hK, hsol, hne⟩ := rf
    have := hK
    have := hsol
    obtain ⟨N, hN, _, comm⟩ := exists_abelian_normal_of_solvable_normal K hne
    have := hN.1
    exact gmp_affine_quotient_bound (by omega) A N hN.2.1 comm R

end GI.Proved
