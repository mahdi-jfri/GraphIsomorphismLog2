module

public import Workspace.Impl.LinAffineResidual
public import Workspace.Cited.AlgoPermGroups

@[expose] public section

/-! Convert the target-stabilizer right coset produced by successive affine
layers to the left-coset convention of canonical answers. -/
namespace GI.Impl
open GI.Cited

variable {G : Type*} [Group G]

def linSourceConjugate (K : Subgroup G) (r : G) : Subgroup G :=
  K.map (MulAut.conj r⁻¹).toMonoidHom

theorem linRightCoset_left (K : Subgroup G) (r : G) :
    (fun k : G => k * r) '' (K : Set G) =
      (fun k : G => r * k) '' (linSourceConjugate K r : Set G) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨r⁻¹ * k * r, ?_, by group⟩
    exact Subgroup.mem_map.mpr ⟨k, hk, by change r⁻¹ * k * (r⁻¹)⁻¹ = r⁻¹ * k * r; simp⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hk
    refine ⟨h, hh, ?_⟩
    change h * r = r * (r⁻¹ * h * (r⁻¹)⁻¹)
    group

def linConjugateGenerators (gs : List G) (r : G) : List G := gs.map fun g => r⁻¹ * g * r

theorem linConjugateGenerators_length (gs : List G) (r : G) :
    (linConjugateGenerators gs r).length = gs.length := List.length_map _

theorem linConjugateGenerators_gens {n : ℕ} (gs : List (Equiv.Perm (Fin n))) (r : Equiv.Perm (Fin n)) :
    gens (linConjugateGenerators gs r) = linSourceConjugate (gens gs) r := by
  unfold gens linSourceConjugate
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp [linConjugateGenerators, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end GI.Impl
