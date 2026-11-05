module

public import Workspace.Impl.LinWreathNumber
public import Workspace.Impl.LinPermCertificate

@[expose] public section

/-! The generating list and representation of the numbered solvable cover. -/
namespace GI.Impl
open GI.Cited Equiv

noncomputable def linWreathSubgens {n : ℕ} (gs : List (Perm (Fin n))) : List (gens gs) :=
  gs.map (linIntoSubgroup (gens gs))

theorem linWreathSubgens_generate {n : ℕ} (gs : List (Perm (Fin n))) :
    Subgroup.closure {g | g ∈ linWreathSubgens gs} = ⊤ := by
  let A := gens gs
  have hmap : (linWreathSubgens gs).map A.subtype = gs :=
    linIntoSubgroup_map A gs (fun g hg => Subgroup.subset_closure hg)
  apply Subgroup.map_injective A.subtype_injective
  have hh : (Subgroup.closure {g | g ∈ linWreathSubgens gs}).map A.subtype = A := by
    rw [MonoidHom.map_closure]
    change Subgroup.closure (A.subtype '' {g | g ∈ linWreathSubgens gs}) = gens gs
    have he : A.subtype '' {g | g ∈ linWreathSubgens gs} = {g | g ∈ gs} := by
      ext g
      simp only [Set.mem_image, Set.mem_setOf_eq, ← hmap, List.mem_map]
    rw [he]
    rfl
  rw [hh]
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
  constructor
  · intro hg
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact g.property

noncomputable def linWreathCoverGenerators {n : ℕ} (gs : List (Perm (Fin n))) :
    List (Perm (Fin (n + n))) :=
  (linWreathGenerators (linWreathSubgens gs)).map (linWreathFinCover (gens gs))

theorem linWreathCoverGenerators_length {n : ℕ} (gs : List (Perm (Fin n))) :
    (linWreathCoverGenerators gs).length = 2 * gs.length + 1 := by
  simp [linWreathCoverGenerators, linWreathSubgens]

theorem linWreathCoverGenerators_gens {n : ℕ} (gs : List (Perm (Fin n))) :
    gens (linWreathCoverGenerators gs) = (linWreathFinCover (gens gs)).range := by
  have hm : {g | g ∈ linWreathCoverGenerators gs} =
      linWreathFinCover (gens gs) '' {g | g ∈ linWreathGenerators (linWreathSubgens gs)} := by
    ext g
    simp only [linWreathCoverGenerators, List.mem_map, Set.mem_image, Set.mem_setOf_eq]
  rw [gens, hm, ← MonoidHom.map_closure, linWreathGenerators_generate _ (linWreathSubgens_generate gs)]
  ext g
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- The actual generated permutation group, rather than just its matrix image,
is solvable. -/
theorem linWreathCoverGenerators_solvable {n : ℕ} (gs : List (Perm (Fin n)))
    (hsol : IsSolvable (gens gs)) : IsSolvable (gens (linWreathCoverGenerators gs)) := by
  rw [linWreathCoverGenerators_gens]
  letI : Group.IsSolvable (gens gs) := hsol
  letI : Group.IsSolvable (gens gs ≀ᵣ linTwo) := linWreath_solvable (H := gens gs)
  exact Group.isSolvable_of_surjective (linWreathFinCover (gens gs)).rangeRestrict_surjective

/-- The numbered cover retains the original wreath element. This is used to
transport its linear representation to the group supplied to VectorStabilizer. -/
noncomputable def linWreathCoverEquiv {n : ℕ} [Nonempty (Fin n)] (gs : List (Perm (Fin n))) :
    (gens gs ≀ᵣ linTwo) ≃* gens (linWreathCoverGenerators gs) := by
  let f := linWreathFinCover (n := n) (gens gs)
  have hi : Function.Injective f := linWreathFinCover_injective
  have hir : Function.Injective f.rangeRestrict := fun x y h => hi (congrArg Subtype.val h)
  exact (MulEquiv.ofBijective f.rangeRestrict ⟨hir, f.rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (linWreathCoverGenerators_gens gs).symm)

end GI.Impl
