module

public import Workspace.RadicalSocleSimpleFactors

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

theorem minimalNormal_of_normal_simple (N : Subgroup G) [N.Normal] [IsSimpleGroup N] :
    MinimalNormal N := by
  refine ⟨inferInstance, (Subgroup.nontrivial_iff_ne_bot N).mp inferInstance, ?_⟩
  intro M hM hMN
  let K := M.comap N.subtype
  haveI : K.Normal := hM.comap N.subtype
  have he : K.map N.subtype = M := Subgroup.map_comap_eq_self (by
    simpa only [Subgroup.range_subtype] using hMN)
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with hb | ht
  · left
    rw [← he, hb, Subgroup.map_bot]
  · right
    rw [← he, ht, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem minimalNormal_normalizer {N : Subgroup G} (hN : MinimalNormal N)
    (K : Subgroup N) [K.Normal] : socle G ≤ (Subgroup.normalizer (K.map N.subtype)) := by
  rw [socle_eq_iSup]
  refine iSup_le fun L => ?_
  by_cases he : L.val = N
  · subst he
    have h := Subgroup.le_normalizer_map (H := K) L.val.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  · apply le_trans ?_ (centralizer_le_normalizer (K.map N.subtype))
    intro l hl m hm
    obtain ⟨k, _, rfl⟩ := hm
    exact minimalNormal_commute hN L.property (Ne.symm he) k ⟨l, hl⟩

def minimalNormalToSocle {N : Subgroup G} (hN : MinimalNormal N) : N →* socle G :=
  Subgroup.inclusion (minimalNormal_le_socle hN)

theorem minimalNormalToSocle_injective {N : Subgroup G} (hN : MinimalNormal N) :
    Function.Injective (minimalNormalToSocle hN) := Subgroup.inclusion_injective _

theorem factor_normal_in_socle {N : Subgroup G} (hN : MinimalNormal N)
    (K : Subgroup N) [K.Normal] : (K.map (minimalNormalToSocle hN)).Normal := by
  constructor
  intro m hm g
  obtain ⟨k, hk, rfl⟩ := hm
  have hkG : (k : G) ∈ K.map N.subtype := ⟨k, hk, rfl⟩
  have hnormal := Subgroup.mem_normalizer_iff.mp (minimalNormal_normalizer hN K g.property)
  have hmem := (hnormal (k : G)).mp hkG
  obtain ⟨k', hk', he⟩ := hmem
  exact ⟨k', hk', Subtype.ext he⟩

theorem simple_factor_minimal_in_socle [Finite G]
    {N : Subgroup G} (hN : MinimalNormal N) (K : MinimalNormals N) :
    MinimalNormal (K.val.map (minimalNormalToSocle hN)) := by
  let f := minimalNormalToSocle hN
  haveI : K.val.Normal := K.property.1
  haveI := minimalNormal_simple_factors hN K
  haveI : (K.val.map f).Normal := factor_normal_in_socle hN K.val
  haveI : Nontrivial (K.val.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
    intro hz
    exact K.property.2.1 ((Subgroup.map_eq_bot_iff_of_injective K.val
      (minimalNormalToSocle_injective hN)).mp hz))
  haveI : IsSimpleGroup (K.val.map f) := IsSimpleGroup.isSimpleGroup_of_surjective
    (f.subgroupMap K.val) (f.subgroupMap_surjective K.val)
  exact minimalNormal_of_normal_simple _

/-- The socle of the socle of any finite group is the whole socle. In
particular, its intrinsic minimal normal subgroups are simple. -/
theorem socle_idempotent [Finite G] : socle (socle G) = ⊤ := by
  let S := socle G
  let D := (socle S).map S.subtype
  haveI : D.Normal := inferInstance
  have hsD : S ≤ D := by
    apply socle_le_normal D
    intro N hN
    let f := minimalNormalToSocle hN
    have hpre : socle N ≤ (socle S).comap f := by
      apply socle_le_normal _
      intro K hK
      intro k hk
      exact minimalNormal_le_socle (simple_factor_minimal_in_socle hN ⟨K, hK⟩)
        ⟨k, hk, rfl⟩
    rw [minimalNormal_socle_eq_top hN] at hpre
    intro n hn
    exact ⟨f ⟨n, hn⟩, hpre (Subgroup.mem_top _), rfl⟩
  have hD : D = S := (Subgroup.map_subtype_le (socle S)).antisymm hsD
  apply Subgroup.map_injective S.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hD

theorem socle_intrinsic_factor_simple [Finite G] (K : MinimalNormals (socle G)) :
    IsSimpleGroup K.val :=
  minimalNormal_simple_of_socle_eq_top socle_idempotent K.property

theorem socle_intrinsic_factor_nonabelian [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    (K : MinimalNormals (socle G)) : ∃ x y : K.val, x * y ≠ y * x :=
  minimalNormal_nonabelian (normal_subgroup_radicalFree radicalFree (socle G)) K.property

noncomputable def socleIntrinsicProductEquiv [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    (∀ K : MinimalNormals (socle G), K.val) ≃* socle G :=
  (socleProductEquiv (normal_subgroup_radicalFree radicalFree (socle G))).trans
    ((MulEquiv.subgroupCongr socle_idempotent).trans Subgroup.topEquiv)

end GI.RadicalSocle
