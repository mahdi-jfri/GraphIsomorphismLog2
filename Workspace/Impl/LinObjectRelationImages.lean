module

public import Workspace.Impl.LinObjectRelations
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-! Coordinate rows generate exactly the image of a local stabilizer.
This bridges the permutation-group output to the integer presentation. -/
namespace GI.Impl
open Matrix

theorem linObjectRelationImage {Q : Type*} [AddCommGroup Q] {s t : ℕ}
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (Z : Matrix (Fin s) (Fin t) ℤ) :
    (linRelations Z).map f = Submodule.span ℤ (Set.range fun i => f (Z i)) := by
  rw [linRelations, range_vecMulLinear, Submodule.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Z i, ⟨i, rfl⟩, rfl⟩

theorem linObjectClosureModule {Q : Type*} [CommGroup Q] {ι : Type*} (v : ι → Q) :
    (Subgroup.closure (Set.range v)).toAddSubgroup.toIntSubmodule =
      Submodule.span ℤ (Set.range fun i => Additive.ofMul (v i)) := by
  rw [Subgroup.toAddSubgroup_closure, AddSubgroup.toIntSubmodule_closure]
  congr 1

theorem linObjectLocalRelationImage {Q : Type*} [CommGroup Q] {s t : ℕ}
    (f : (Fin t → ℤ) →ₗ[ℤ] Additive Q) (Z : Matrix (Fin s) (Fin t) ℤ)
    (v : Fin s → Q) (hZ : ∀ i, f (Z i) = Additive.ofMul (v i)) :
    (linRelations Z).map f = (Subgroup.closure (Set.range v)).toAddSubgroup.toIntSubmodule := by
  rw [linObjectRelationImage, linObjectClosureModule]
  congr 1
  exact congrArg Set.range (funext hZ)

end GI.Impl
