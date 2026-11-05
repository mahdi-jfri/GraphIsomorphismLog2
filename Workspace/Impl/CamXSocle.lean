module

public import Workspace.Impl.CamXFactors
public import Workspace.Impl.CamSmallM

@[expose] public section

/-!
# Basic properties of the socle of a Maróti group

Let `G` be primitive with a Maróti structure `e`, and let `N = camProd e univ ≅ Alt(m)^r`.
This file proves that `N ≤ G` (`camX_socle_le`), `G` normalizes `N` (`camX_socle_normal`),
and any nontrivial normal subgroup of `G` is transitive (`camX_normal_transitive`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-- The socle `camProd e univ` lies in `G`. -/
theorem camX_socle_le {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e) :
    camProd e Finset.univ ≤ G := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := camX_mem_prod.mp hg
  exact hM.2 h fun i => (hh i).1 (Finset.mem_univ i)

/-- `G` normalizes the socle: conjugating by `g` permutes the coordinates and conjugates each
one by a permutation of `Fin m`. -/
theorem camX_socle_normal {G : Subgroup (Perm (Fin n))} (hM : MarotiStructure G e) :
    ∀ g ∈ G, ∀ y ∈ camProd e Finset.univ, g * y * g⁻¹ ∈ camProd e Finset.univ := by
  intro g hg y hy
  obtain ⟨σ, h, hgh⟩ := hM.1 g hg
  obtain ⟨b, hb, rfl⟩ := camX_mem_prod.mp hy
  let b' : Fin r → Perm (Fin m) := fun i => h i * b (σ i) * (h i)⁻¹
  have hcomm : g * camHom e b = camHom e b' * g := by
    refine Equiv.ext fun w => e.injective (funext fun i => ?_)
    rw [Perm.mul_apply, Perm.mul_apply, hgh, camHom_apply, camHom_apply, hgh]
    change kSetPerm (h i) (kSetPerm (b (σ i)) (e w (σ i))) =
      kSetPerm (h i * b (σ i) * (h i)⁻¹) (kSetPerm (h i) (e w (σ i)))
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← cam_kSetPerm_mul, ← cam_kSetPerm_mul,
      inv_mul_cancel_right]
  rw [hcomm, mul_inv_cancel_right]
  refine camX_mem_prod.mpr ⟨b', fun i => ⟨fun _ => ?_, fun hi => absurd (Finset.mem_univ i) hi⟩,
    rfl⟩
  exact (alternatingGroup.normal (α := Fin m)).conj_mem _ ((hb (σ i)).1 (Finset.mem_univ _)) (h i)

/-- A nontrivial subgroup of `Perm (Fin n)` inside the primitive group `G` and normalized by `G`
is transitive (Mathlib's `IsPreprimitive.isQuasiPreprimitive`). -/
theorem camX_normal_transitive {G M : Subgroup (Perm (Fin n))}
    (hprim : MulAction.IsPreprimitive G (Fin n)) (hMG : M ≤ G) (hM : M ≠ ⊥)
    (hMn : ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M) (x y : Fin n) : ∃ g ∈ M, g x = y := by
  let N : Subgroup G := M.subgroupOf G
  haveI : N.Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hMn g g.2 a ha⟩
  have hfix : MulAction.fixedPoints N (Fin n) ≠ Set.univ := by
    obtain ⟨⟨g, hgM⟩, hg1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
    have hg1 : g ≠ 1 := fun h => hg1' (Subtype.ext h)
    obtain ⟨z, hz⟩ : ∃ z, g z ≠ z := by
      by_contra hcon
      push Not at hcon
      exact hg1 (Equiv.ext hcon)
    intro hall
    have hzfix : z ∈ MulAction.fixedPoints N (Fin n) := hall ▸ Set.mem_univ z
    exact hz (hzfix ⟨⟨g, hMG hgM⟩, (Subgroup.mem_subgroupOf).mpr hgM⟩)
  haveI := MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfix
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N x y
  exact ⟨g.1.1, (Subgroup.mem_subgroupOf).mp g.2, hg⟩

end GI.Impl
