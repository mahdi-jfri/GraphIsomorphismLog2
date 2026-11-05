module

public import Workspace.Impl.LinObjectRelationImages
public import Workspace.Impl.LinPermCertificate

@[expose] public section

/-! The local image module depends on the subgroup, rather than on the
particular generating list returned by a cited algorithm. -/
namespace GI.Impl
open GI.Cited

noncomputable def linObjectGroupImage {n : ℕ} {Q : Type*} [CommGroup Q]
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q) (B : Subgroup (Equiv.Perm (Fin n))) :
    Submodule ℤ (Additive Q) := ((B.subgroupOf A).map π).toAddSubgroup.toIntSubmodule

theorem linObjectSubgroupGenerators {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (bs : List (Equiv.Perm (Fin n))) (hBA : gens bs ≤ A) :
    Subgroup.closure (Set.range fun i : Fin bs.length => linIntoSubgroup A (bs.get i)) =
      (gens bs).subgroupOf A := by
  have hm : ∀ i : Fin bs.length, bs.get i ∈ A := fun i =>
    hBA (Subgroup.subset_closure (List.get_mem _ _))
  apply Subgroup.map_injective A.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hBA]
  have he : A.subtype '' Set.range (fun i : Fin bs.length => linIntoSubgroup A (bs.get i)) =
      {g | g ∈ bs} := by
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      simpa only [Set.mem_setOf_eq, linIntoSubgroup_val A _ (hm i)] using List.get_mem bs i
    · intro hg
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
      exact ⟨linIntoSubgroup A (bs.get i), ⟨i, rfl⟩, linIntoSubgroup_val A _ (hm i)⟩
  rw [he]
  rfl

theorem linObjectGroupImage_generators {n : ℕ} {Q : Type*} [CommGroup Q]
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (bs : List (Equiv.Perm (Fin n))) (hBA : gens bs ≤ A) :
    linObjectGroupImage A π (gens bs) = Submodule.span ℤ
      (Set.range fun i : Fin bs.length => Additive.ofMul (π (linIntoSubgroup A (bs.get i)))) := by
  unfold linObjectGroupImage
  rw [← linObjectSubgroupGenerators A bs hBA, MonoidHom.map_closure, ← Set.range_comp]
  exact linObjectClosureModule _

theorem linObjectGens_one {n : ℕ} (bs : List (Equiv.Perm (Fin n))) : gens (1 :: bs) = gens bs := by
  have he : {g : Equiv.Perm (Fin n) | g ∈ 1 :: bs} = insert 1 {g | g ∈ bs} := by
    ext g
    simp
  unfold gens
  rw [he, Subgroup.closure_insert_one]

theorem linObjectGroupImage_identityGenerators {n : ℕ} {Q : Type*} [CommGroup Q]
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (bs : List (Equiv.Perm (Fin n))) (hBA : gens bs ≤ A) :
    linObjectGroupImage A π (gens bs) = Submodule.span ℤ
      (Set.range fun i : Fin (1 :: bs).length =>
        Additive.ofMul (π (linIntoSubgroup A ((1 :: bs).get i)))) := by
  have hh := linObjectGroupImage_generators A π (1 :: bs)
    (by rw [linObjectGens_one]; exact hBA)
  simpa only [linObjectGens_one] using hh

end GI.Impl
