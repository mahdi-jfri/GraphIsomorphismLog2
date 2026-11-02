import Workspace.Impl.LinObjectGroupImage
import Workspace.Impl.LinObjectStabilizers

/-! Quotient coordinates remember exactly the local stabilizer coset.
Containing the kernel is the hypothesis that permits recovery of an
actual permutation statement from an additive residue statement. -/
namespace GI.Impl
open GI.Cited GI.Multicoset

theorem linObject_mem_image_iff {G Q : Type*} [Group G] [Group Q]
    (π : G →* Q) (C : Subgroup G) (hker : π.ker ≤ C) (a : G) :
    π a ∈ C.map π ↔ a ∈ C := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hk : b⁻¹ * a ∈ π.ker := by
      change π (b⁻¹ * a) = 1
      rw [map_mul, map_inv, hba, inv_mul_cancel]
    have hh := C.mul_mem hb (hker hk)
    simpa only [mul_inv_cancel_left] using hh
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem linObject_groupImage_mem_iff {n : ℕ} {Q : Type*} [CommGroup Q]
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (C : Subgroup (Equiv.Perm (Fin n))) (hker : π.ker ≤ C.subgroupOf A) (a : A) :
    Additive.ofMul (π a) ∈ linObjectGroupImage A π C ↔ a.val ∈ C := by
  change π a ∈ (C.subgroupOf A).map π ↔ a ∈ C.subgroupOf A
  exact linObject_mem_image_iff π (C.subgroupOf A) hker a

theorem linObject_groupImage_sub_iff {n : ℕ} {Q : Type*} [CommGroup Q]
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (C : Subgroup (Equiv.Perm (Fin n))) (hker : π.ker ≤ C.subgroupOf A) (a b : A) :
    Additive.ofMul (π a) - Additive.ofMul (π b) ∈ linObjectGroupImage A π C ↔
      a.val * b.val⁻¹ ∈ C := by
  have he : Additive.ofMul (π a) - Additive.ofMul (π b) =
      Additive.ofMul (π (a * b⁻¹)) := by
    rw [map_mul, map_inv, sub_eq_add_neg]
    rfl
  rw [he]
  exact linObject_groupImage_mem_iff A π C hker (a * b⁻¹)

theorem linObject_act_eq_iff_image {n : ℕ} {Q Ω : Type*} [CommGroup Q]
    [RAct (Equiv.Perm (Fin n)) Ω] (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (T : Multiset Ω)
    (hker : π.ker ≤ (Aut A T).subgroupOf A) (a b : A) :
    T ↼ a.val = T ↼ b.val ↔
      Additive.ofMul (π a) - Additive.ofMul (π b) ∈ linObjectGroupImage A π (Aut A T) := by
  rw [linObject_groupImage_sub_iff A π (Aut A T) hker]
  constructor
  · intro he
    exact ⟨A.mul_mem a.property (A.inv_mem b.property), by
      rw [← act_act, he, act_act_inv]⟩
  · intro hab
    have hh := congrArg (fun Z => Z ↼ b.val) hab.2
    simpa only [act_act, inv_mul_cancel_right] using hh

end GI.Impl
