module

public import Workspace.RadicalSocleDecomposition

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

/-- Ambient conjugation is transitive on the simple factors of each
minimal normal subgroup. This is proved by normal closure and centralizers,
without an O'Nan--Scott or classification theorem. -/
theorem minimalNormal_factors_conjugate [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) (K L : MinimalNormals N) :
    ∃ g : G, K.val.map (@MulAut.conjNormal G _ N hN.1 g).toMonoidHom = L.val := by
  classical
  letI := hN.1
  by_contra hn
  push Not at hn
  let M : Subgroup G := K.val.map N.subtype
  let D := Subgroup.normalClosure (M : Set G)
  have hDN : D ≤ N := Subgroup.normalClosure_le_normal (Subgroup.map_subtype_le K.val)
  have hDne : D ≠ ⊥ := by
    intro hz
    have hm : M = ⊥ := le_bot_iff.mp (hz ▸ (Subgroup.le_normalClosure (H := M)))
    exact K.property.2.1 ((Subgroup.map_eq_bot_iff_of_injective K.val
      N.subtype_injective).mp hm)
  have hDeq : D = N := (hN.2.2 D inferInstance hDN).resolve_left hDne
  have hDC : D ≤ Subgroup.centralizer ((L.val.map N.subtype) : Set G) := by
    change Subgroup.closure (Group.conjugatesOfSet (M : Set G)) ≤ _
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    intro z hz
    obtain ⟨l, hl, rfl⟩ := hz
    have he := minimalNormal_commute L.property
      (K.property.map (MulAut.conjNormal (H := N) g)) (Ne.symm (hn g))
      ⟨l, hl⟩ ⟨MulAut.conjNormal g k, ⟨k, hk, rfl⟩⟩
    exact congrArg (fun z : N => (z : G)) he
  have hLcenter : L.val ≤ Subgroup.center N := by
    intro l hl
    apply Subgroup.mem_center_iff.mpr
    intro n
    have hnD : (n : G) ∈ D := by rw [hDeq]; exact n.property
    exact Subtype.ext ((hDC hnD l ⟨l, hl, rfl⟩).symm)
  rw [minimalNormal_center_eq_bot radicalFree hN] at hLcenter
  exact L.property.2.1 (le_bot_iff.mp hLcenter)

noncomputable def minimalNormalFactorEquiv [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) (K L : MinimalNormals N) : K.val ≃* L.val := by
  letI := hN.1
  let g := Classical.choose (minimalNormal_factors_conjugate radicalFree hN K L)
  exact ((MulAut.conjNormal (H := N) g).subgroupMap K.val).trans
    (MulEquiv.subgroupCongr
      (Classical.choose_spec (minimalNormal_factors_conjugate radicalFree hN K L)))

/-- Each actual minimal normal subgroup is a power of one of its actual
finite nonabelian simple factors. -/
noncomputable def minimalNormalPowerEquiv [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) (K : MinimalNormals N) :
    (MinimalNormals N → K.val) ≃* N :=
  (MulEquiv.piCongrRight (fun L => minimalNormalFactorEquiv radicalFree hN K L)).trans
    (minimalNormalProductEquiv radicalFree hN)

theorem minimalNormal_card_power [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) (K : MinimalNormals N) :
    Nat.card N = Nat.card K.val ^ Nat.card (MinimalNormals N) := by
  rw [← Nat.card_congr (minimalNormalPowerEquiv radicalFree hN K).toEquiv, Nat.card_fun]

/-- Existence of the base simple factor is also proved, so the homogeneous
decomposition does not require a supplied structural witness. -/
theorem minimalNormal_exists_simple_power [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)
    {N : Subgroup G} (hN : MinimalNormal N) :
    ∃ K : MinimalNormals N, IsSimpleGroup K.val ∧
      (∃ x y : K.val, x * y ≠ y * x) ∧
      Nonempty ((MinimalNormals N → K.val) ≃* N) := by
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  obtain ⟨K, hK, _⟩ := exists_minimal_normal_le (⊤ : Subgroup N) top_ne_bot
  exact ⟨⟨K, hK⟩, minimalNormal_simple_factors hN ⟨K, hK⟩,
    minimalNormal_factors_nonabelian radicalFree hN ⟨K, hK⟩,
    ⟨minimalNormalPowerEquiv radicalFree hN ⟨K, hK⟩⟩⟩

end GI.RadicalSocle
