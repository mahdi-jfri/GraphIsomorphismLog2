module

public import Workspace.Proved.PalfyLinear
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent

/-!
# Sylow subgroups of linear groups

For every subgroup `G ≤ GL(V)` and every prime `r` other than the characteristic, the `r`-part of
`|G|` is at most `|V|^23` (`GI.Degree.sylow_cube_le`). A Sylow `r`-subgroup is solvable, and its
order is invertible in the field, so it is completely reducible by Maschke
(`GI.Degree.palfyCR_of_coprime`), and `GI.Proved.palfyLinear_card` applies.
-/

@[expose] public section

namespace GI.Degree

open GI.Proved

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- **Maschke.** A linear group whose order is invertible in the field is completely reducible. -/
theorem palfyCR_of_coprime [Finite V] (P : Subgroup (Module.End K V)ˣ) [Finite P]
    (h : (Nat.card P : K) ≠ 0) : palfyCR P := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  intro W hW
  obtain ⟨W₀, hc⟩ := Submodule.exists_isCompl W
  let π : V →ₗ[K] V := W.subtype ∘ₗ Submodule.linearProjOfIsCompl W W₀ hc
  have hπW : ∀ v, π v ∈ W := fun v => (Submodule.linearProjOfIsCompl W W₀ hc v).2
  have hπid : ∀ w ∈ W, π w = w := fun w hw => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
  let ρ₀ : Module.End K V :=
    ∑ g : P, ((g : (Module.End K V)ˣ) : Module.End K V) * π *
      (((g⁻¹ : P) : (Module.End K V)ˣ) : Module.End K V)
  have hcomm : ∀ p : P, ((p : (Module.End K V)ˣ) : Module.End K V) * ρ₀ =
      ρ₀ * ((p : (Module.End K V)ˣ) : Module.End K V) := by
    intro p
    simp only [ρ₀, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft p) _ _ fun g => ?_
    have e : (((p * g)⁻¹ : P) : (Module.End K V)ˣ) = ((g⁻¹ : P) : (Module.End K V)ˣ) * (p⁻¹ : P) := by
      simp
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul, e, mul_assoc]
    congr 3
    rw [← Units.val_mul, ← Subgroup.coe_mul]
    simp
  have hρW : ∀ v, ρ₀ v ∈ W := fun v => by
    simp only [ρ₀, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun g _ => ?_
    exact hW g g.2 _ (hπW _)
  have hρid : ∀ w ∈ W, ρ₀ w = (Nat.card P : K) • w := fun w hw => by
    simp only [ρ₀, LinearMap.sum_apply]
    have : ∀ g : P, (((g : (Module.End K V)ˣ) : Module.End K V) * π *
        (((g⁻¹ : P) : (Module.End K V)ˣ) : Module.End K V)) w = w := by
      intro g
      have hgw : (((g⁻¹ : P) : (Module.End K V)ˣ) : Module.End K V) w ∈ W := hW _ (g⁻¹).2 _ hw
      simp only [Module.End.mul_apply]
      rw [hπid _ hgw, ← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul]
      simp
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  let c : K := (Nat.card P : K)⁻¹
  have hproj : LinearMap.IsProj W (c • ρ₀) := by
    refine ⟨fun v => W.smul_mem _ (hρW v), fun w hw => ?_⟩
    rw [LinearMap.smul_apply, hρid w hw, smul_smul, inv_mul_cancel₀ h, one_smul]
  refine ⟨LinearMap.ker (c • ρ₀), ?_, hproj.isCompl⟩
  intro p hp v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h1 : (c • ρ₀) (((p : (Module.End K V)ˣ) : Module.End K V) v) =
      c • (ρ₀ * ((p : (Module.End K V)ˣ) : Module.End K V)) v := rfl
  rw [h1, ← hcomm ⟨p, hp⟩, Module.End.mul_apply, ← map_smul]
  have h2 : c • ρ₀ v = 0 := hv
  rw [h2, map_zero]

/-- The `r`-part of the order of a linear group, for `r` other than the characteristic. -/
theorem sylow_cube_le [Finite K] [Finite V] [Nontrivial V] (G : Subgroup (Module.End K V)ˣ)
    (r : ℕ) [hr : Fact r.Prime] (hK : (r : K) ≠ 0) :
    (r ^ (Nat.card G).factorization r) ^ 3 ≤ Nat.card V ^ 69 := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow r G) := inferInstance
  have hP := Sylow.card_eq_multiplicity P
  let P' : Subgroup (Module.End K V)ˣ := (P : Subgroup G).map G.subtype
  have hcard : Nat.card P' = Nat.card (P : Subgroup G) :=
    (Nat.card_congr ((P : Subgroup G).equivMapOfInjective _ G.subtype_injective).toEquiv).symm
  have hgrp : IsPGroup r P' := by
    have := P.isPGroup
    exact this.map G.subtype
  have hs : Group.IsSolvable P' := by
    have : Finite P' := inferInstance
    have := hgrp.isNilpotent
    infer_instance
  have hne : (Nat.card P' : K) ≠ 0 := by
    rw [hcard, hP]
    push_cast
    exact pow_ne_zero _ hK
  have h := palfyLinear K V P' hs (palfyCR_of_coprime P' hne)
  rw [hcard, hP] at h
  have h1 : 1 ≤ 24 * Nat.card K ^ 6 := Nat.mul_pos (by norm_num) (pow_pos Nat.card_pos 6)
  exact (Nat.le_mul_of_pos_left _ h1).trans h

end GI.Degree
