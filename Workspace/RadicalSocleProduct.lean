module

public import Workspace.RadicalSocleStructure
public import Mathlib.GroupTheory.NoncommPiCoprod

@[expose] public section

namespace GI.RadicalSocle

variable {G : Type*} [Group G]

/-- The index set consists of the actual minimal normal subgroups. -/
abbrev MinimalNormals (G : Type*) [Group G] := {N : Subgroup G // MinimalNormal N}

theorem normal_iSup {ι : Type*} (H : ι → Subgroup G)
    (h : ∀ i, (H i).Normal) : (⨆ i, H i).Normal := by
  constructor
  intro x hx g
  refine Subgroup.iSup_induction H (C := fun y => g * y * g⁻¹ ∈ ⨆ i, H i) hx ?_ ?_ ?_
  · intro i y hy
    exact (le_iSup H i) ((h i).conj_mem y hy g)
  · simpa only [mul_one, mul_inv_cancel] using (⨆ i, H i).one_mem
  · intro y z hy hz
    rw [← conj_mul]
    exact (⨆ i, H i).mul_mem hy hz

theorem socle_eq_iSup : socle G = ⨆ N : MinimalNormals G, N.val := by
  haveI : (⨆ N : MinimalNormals G, N.val).Normal :=
    normal_iSup _ (fun N => N.property.1)
  apply le_antisymm
  · exact socle_le_normal _ (fun N hN => le_iSup (fun M : MinimalNormals G => M.val) ⟨N, hN⟩)
  · exact iSup_le fun N => minimalNormal_le_socle N.property

theorem minimalNormals_commute :
    Pairwise fun M N : MinimalNormals G =>
      ∀ x y : G, x ∈ M.val → y ∈ N.val → Commute x y := by
  intro M N hne x y hx hy
  exact minimalNormal_commute M.property N.property
    (fun h => hne (Subtype.ext h)) ⟨x, hx⟩ ⟨y, hy⟩

/-- Pairwise intersections alone do not prove a direct product. Independence
follows because the other factors centralize this factor and its center is
trivial. -/
theorem minimalNormals_independent
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    iSupIndep (fun N : MinimalNormals G => N.val) := by
  intro N
  have hc : (⨆ (M : MinimalNormals G) (_ : M ≠ N), M.val) ≤
      Subgroup.centralizer (N.val : Set G) := by
    refine iSup_le fun M => iSup_le fun hMN => ?_
    intro y hy x hx
    exact minimalNormals_commute (Ne.symm hMN) x y hx hy
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : N.val) ∈ Subgroup.center N.val := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc hx.2 y y.property)
  rw [minimalNormal_center_eq_bot radicalFree N.property, Subgroup.mem_bot] at hxcenter
  exact congrArg (fun y : N.val => (y : G)) hxcenter

noncomputable def socleProductHom [Finite G] :
    (∀ N : MinimalNormals G, N.val) →* G := by
  letI := Fintype.ofFinite (MinimalNormals G)
  exact Subgroup.noncommPiCoprod minimalNormals_commute

theorem socleProductHom_range [Finite G] :
    (socleProductHom (G := G)).range = socle G := by
  letI := Fintype.ofFinite (MinimalNormals G)
  unfold socleProductHom
  rw [Subgroup.noncommPiCoprod_range, socle_eq_iSup]

theorem socleProductHom_injective [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    Function.Injective (socleProductHom (G := G)) := by
  letI := Fintype.ofFinite (MinimalNormals G)
  unfold socleProductHom
  exact Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (minimalNormals_independent radicalFree)

/-- An actual direct-product equivalence, with no decomposition data supplied
as a hypothesis. The factors here are minimal normal subgroups; their simple
factor decomposition is a separate step. -/
noncomputable def socleProductEquiv [Finite G]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    (∀ N : MinimalNormals G, N.val) ≃* socle G :=
  (MonoidHom.ofInjective (socleProductHom_injective radicalFree)).trans
    (MulEquiv.subgroupCongr socleProductHom_range)

theorem socle_card_product [Finite G] [Fintype (MinimalNormals G)]
    (radicalFree : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥) :
    Nat.card (socle G) = ∏ N : MinimalNormals G, Nat.card N.val := by
  rw [← Nat.card_congr (socleProductEquiv radicalFree).toEquiv, Nat.card_pi]

noncomputable def radical_quotient_socleProductEquiv [Finite G] :
    (∀ N : MinimalNormals (G ⧸ solvableRadical G), N.val) ≃*
      socle (G ⧸ solvableRadical G) :=
  socleProductEquiv radical_quotient_radicalFree

end GI.RadicalSocle
