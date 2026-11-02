import Workspace.Impl.LinPresentation
import Mathlib.LinearAlgebra.Isomorphisms

/-! Appending relation generators constructs the quotients A/B_i and W/D.
The equivalence sends an integer coordinate vector to its original image,
followed by the new quotient map. -/
namespace GI.Impl

variable {Q : Type*} [AddCommGroup Q] {d : ℕ}

/-- The kernel after imposing further integer relations is the sum of the
old relation module and the span of the new coordinate vectors. -/
theorem linPresentationExtend_ker (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (U : Submodule ℤ (Fin d → ℤ)) :
    LinearMap.ker (((U.map f).mkQ).comp f) = LinearMap.ker f ⊔ U := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, sup_comm]

/-- A presentation stays exact after appending relations. -/
noncomputable def linPresentationExtendEquiv (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (U : Submodule ℤ (Fin d → ℤ)) :
    ((Fin d → ℤ) ⧸ (LinearMap.ker f ⊔ U)) ≃ₗ[ℤ] (Q ⧸ U.map f) := by
  let g := (U.map f).mkQ.comp f
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp hf
  exact (Submodule.quotEquivOfEq _ _ (linPresentationExtend_ker f U).symm).trans
    (g.quotKerEquivOfSurjective hg)

@[simp] theorem linPresentationExtendEquiv_mk (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (U : Submodule ℤ (Fin d → ℤ)) (z : Fin d → ℤ) :
    linPresentationExtendEquiv f hf U ((LinearMap.ker f ⊔ U).mkQ z) =
      (U.map f).mkQ (f z) := by
  rfl

end GI.Impl
