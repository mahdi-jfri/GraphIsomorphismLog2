import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic

/-! Correct every generator of the liftable preimage and retain the
kernel. Equality of quotient images then proves that no automorphisms
are lost. This is the generator argument in A.20. -/
namespace GI.Impl

variable {G Q : Type*} [Group G] [Group Q]

theorem linSubgroup_eq_of_map_and_kernel (π : G →* Q) (L S : Subgroup G)
    (hLS : L ≤ S) (hmap : L.map π = S.map π) (hker : π.ker ⊓ S ≤ L) : L = S := by
  apply le_antisymm hLS
  intro x hx
  have himg : π x ∈ L.map π := by
    rw [hmap]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := himg
  have hk : y⁻¹ * x ∈ π.ker ⊓ S := by
    constructor
    · change π (y⁻¹ * x) = 1
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    · exact S.mul_mem (S.inv_mem (hLS hy)) hx
  have hh := L.mul_mem hy (hker hk)
  simpa only [mul_inv_cancel_left] using hh

/-- The corrected generators and the kernel generate the whole subgroup.
All original quotient generators must have a corrected lift. -/
theorem linObjectCorrectedGenerators_eq {ι : Type*} (π : G →* Q)
    (original corrected : ι → G) (S K : Subgroup G)
    (hS : S ≤ Subgroup.closure (Set.range original)) (hKS : K ≤ S)
    (hker : π.ker ⊓ S ≤ K) (hcorrected : ∀ i, corrected i ∈ S)
    (himage : ∀ i, π (corrected i) = π (original i)) :
    Subgroup.closure (Set.range corrected) ⊔ K = S := by
  let L := Subgroup.closure (Set.range corrected) ⊔ K
  have hLS : L ≤ S := sup_le ((Subgroup.closure_le S).mpr (by
    rintro x ⟨i, rfl⟩
    exact hcorrected i)) hKS
  apply linSubgroup_eq_of_map_and_kernel π L S hLS
  · apply le_antisymm (Subgroup.map_mono hLS)
    have hC : Subgroup.closure (Set.range original) ≤ (L.map π).comap π := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      change π (original i) ∈ L.map π
      rw [← himage i]
      have hc : corrected i ∈ Subgroup.closure (Set.range corrected) :=
        Subgroup.subset_closure ⟨i, rfl⟩
      exact ⟨corrected i, (show Subgroup.closure (Set.range corrected) ≤ L from le_sup_left) hc, rfl⟩
    exact Subgroup.map_le_iff_le_comap.mpr (hS.trans hC)
  · exact hker.trans le_sup_right

/-- Multiplying a preimage generator by an element in the kernel keeps
its quotient image, as needed for the common-translation correction. -/
theorem linObjectCorrection_image (π : G →* Q) (g a : G) (ha : a ∈ π.ker) :
    π (g * a) = π g := by
  rw [map_mul, MonoidHom.mem_ker.mp ha, mul_one]

end GI.Impl
