import Workspace.Impl.LinObjectNormalMath

/-! Finite coordinates for W before quotienting by the diagonal. These
coordinates retain the full offset needed for the final correction lift. -/
namespace GI.Impl
open Matrix

noncomputable def linObjectProductMatrixEquiv {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i)) :
    ((Fin (d * p) → ℤ) ⧸ linRelations (linObjectBlockMatrix M)) ≃ₗ[ℤ]
      (∀ i, Q ⧸ B i) := by
  let g := (linObjectProductMap B f).comp (linObjectUnflatten p d).toLinearMap
  have hg : Function.Surjective g :=
    (linObjectProductMap_surjective B f hf).comp (linObjectUnflatten p d).surjective
  exact (Submodule.quotEquivOfEq _ _ (linObjectBlockPresentation_ker B f M hM).symm).trans
    (g.quotKerEquivOfSurjective hg)

@[simp] theorem linObjectProductMatrixEquiv_mk {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i))
    (z : Fin (d * p) → ℤ) :
    linObjectProductMatrixEquiv B f hf M hM
      ((linRelations (linObjectBlockMatrix M)).mkQ z) =
      linObjectProductMap B f (linObjectUnflatten p d z) := rfl

noncomputable def linObjectProductNormalEquiv {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i))
    (V D : Matrix (Fin (d * p)) (Fin (d * p)) ℤ) (hV : IsUnit V.det)
    (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z (linObjectBlockMatrix M) = x) ↔
      ∀ i, D i i ∣ (Matrix.vecMul x V) i) :
    (∀ i, Q ⧸ B i) ≃+ tmGLVec (tmGLQMod D) :=
  (linObjectProductMatrixEquiv B f hf M hM).symm.toAddEquiv.trans
    (tmGLQOutEquiv hV hpos hD)

theorem linObjectProductNormalEquiv_mk {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i))
    (V D : Matrix (Fin (d * p)) (Fin (d * p)) ℤ) (hV : IsUnit V.det)
    (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z (linObjectBlockMatrix M) = x) ↔
      ∀ i, D i i ∣ (Matrix.vecMul x V) i) (z : Fin (d * p) → ℤ) :
    linObjectProductNormalEquiv B f hf M hM V D hV hpos hD
      (linObjectProductMap B f (linObjectUnflatten p d z)) = tmGLQMap V D z := by
  rw [← linObjectProductMatrixEquiv_mk B f hf M hM z]
  change tmGLQOutEquiv hV hpos hD
    ((linObjectProductMatrixEquiv B f hf M hM).symm
      (linObjectProductMatrixEquiv B f hf M hM
        ((linRelations (linObjectBlockMatrix M)).mkQ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact tmGLQOutEquiv_mk hV hpos hD z

end GI.Impl
