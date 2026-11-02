import Workspace.Impl.LinObjectRecordsSpec
import Workspace.Impl.LinAffineCallerSpec

namespace GI.Impl
open GI.Cited GI.Lang

@[simp] theorem linObjectAffineRecord_item {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) (g : gens gs) :
    linObjectAffineRecord m ρ c g = tmGLAffItem gs m ρ c g := rfl

theorem linObjectAffineRecords_encoding {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) :
    (gs.map fun g => linObjectAffineRecord m ρ c (linIntoSubgroup (gens gs) g)) =
      (gs.attach.map fun g => tmGLAffItem gs m ρ c ⟨g.val,Subgroup.subset_closure g.property⟩) := by
  calc
    _ = gs.attach.map (fun g => linObjectAffineRecord m ρ c (linIntoSubgroup (gens gs) g.val)) :=
      List.attach_map_val.symm
    _ = _ := by
      apply List.map_congr_left
      intro a ha
      have he : linIntoSubgroup (gens gs) a.val = ⟨a.val,Subgroup.subset_closure a.property⟩ :=
        Subtype.ext (linIntoSubgroup_val (gens gs) a.val (Subgroup.subset_closure a.property))
      rw [he]
      rfl

end GI.Impl
