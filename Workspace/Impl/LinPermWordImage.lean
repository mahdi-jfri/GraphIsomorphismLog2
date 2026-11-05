module

public import Workspace.Impl.LinPermWord
public import Workspace.Impl.LinPermCertificate

@[expose] public section

namespace GI.Impl
open GI.Cited

theorem linPermWord_mem {n : ℕ} (as : List (Equiv.Perm (Fin n))) (z : Fin as.length → ℤ) :
    linGroupWord (fun i => as.get i) z ∈ gens as :=
  linGroupWord_mem (gens as) _ (fun i => Subgroup.subset_closure (List.get_mem as i)) z

theorem linPermWord_image {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (z : Fin as.length → ℤ) :
    π ⟨linGroupWord (fun i => as.get i) z, linPermWord_mem as z⟩ =
      linCoordHom (fun i => π (linIntoSubgroup (gens as) (as.get i))) (Multiplicative.ofAdd z) := by
  let v : Fin as.length → gens as := fun i => linIntoSubgroup (gens as) (as.get i)
  have hv (i : Fin as.length) : (v i).val = as.get i :=
    linIntoSubgroup_val _ _ (Subgroup.subset_closure (List.get_mem as i))
  have hval : (linGroupWord v z).val = linGroupWord (fun i => as.get i) z := by
    change (gens as).subtype (linGroupWord v z) = _
    rw [linGroupWord_map]
    congr 1
    exact funext hv
  have he : linGroupWord v z =
      ⟨linGroupWord (fun i => as.get i) z, linPermWord_mem as z⟩ := Subtype.ext hval
  have hh := linGroupWord_image π v z
  rw [he] at hh
  exact hh

theorem linPermWord_coordinates {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) (z : Fin as.length → ℤ) :
    linCoordMap (fun i => π (linIntoSubgroup (gens as) (as.get i))) z =
      Additive.ofMul (π ⟨linGroupWord (fun i => as.get i) z, linPermWord_mem as z⟩) := by
  exact (congrArg Additive.ofMul (linPermWord_image as π z)).symm

end GI.Impl
