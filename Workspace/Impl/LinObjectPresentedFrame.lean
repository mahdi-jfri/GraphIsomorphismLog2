import Workspace.Impl.LinObjectFrameMath

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectPresentedQuotient {r d : ℕ} {R : Type*} [AddCommGroup R]
    (M : Matrix (Fin r) (Fin d) ℤ) (f : (Fin d → ℤ) →ₗ[ℤ] R)
    (hf : Function.Surjective f) (hk : LinearMap.ker f = linRelations M) :
    ((Fin d → ℤ) ⧸ linRelations M) ≃ₗ[ℤ] R :=
  (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

@[simp] theorem linObjectPresentedQuotient_mk {r d : ℕ} {R : Type*} [AddCommGroup R]
    (M : Matrix (Fin r) (Fin d) ℤ) (f : (Fin d → ℤ) →ₗ[ℤ] R)
    (hf : Function.Surjective f) (hk : LinearMap.ker f = linRelations M) (z : Fin d → ℤ) :
    linObjectPresentedQuotient M f hf hk ((linRelations M).mkQ z) = f z := rfl

noncomputable def linObjectPresentedFrame {r d : ℕ} {R : Type*} [AddCommGroup R]
    (M : Matrix (Fin r) (Fin d) ℤ) (f : (Fin d → ℤ) →ₗ[ℤ] R)
    (hf : Function.Surjective f) (hk : LinearMap.ker f = linRelations M)
    (V D : Matrix (Fin d) (Fin d) ℤ) (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i) :
    R ≃+ tmGLVec (tmGLQMod D) :=
  (linObjectPresentedQuotient M f hf hk).symm.toAddEquiv.trans (tmGLQOutEquiv hV hpos hD)

theorem linObjectPresentedFrame_image {r d : ℕ} {R : Type*} [AddCommGroup R]
    (M : Matrix (Fin r) (Fin d) ℤ) (f : (Fin d → ℤ) →ₗ[ℤ] R)
    (hf : Function.Surjective f) (hk : LinearMap.ker f = linRelations M)
    (V D : Matrix (Fin d) (Fin d) ℤ) (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z M = x) ↔ ∀ i, D i i ∣ (Matrix.vecMul x V) i)
    (z : Fin d → ℤ) : linObjectPresentedFrame M f hf hk V D hV hpos hD (f z) = tmGLQMap V D z := by
  rw [← linObjectPresentedQuotient_mk M f hf hk z]
  change tmGLQOutEquiv hV hpos hD
    ((linObjectPresentedQuotient M f hf hk).symm
      (linObjectPresentedQuotient M f hf hk ((linRelations M).mkQ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact tmGLQOutEquiv_mk hV hpos hD z

/-- A normal-form output supplies the frame required by the evaluator,
for every surjective map with the certified row-relation kernel. -/
theorem linObjectNormalFrame_exists {r d : ℕ} {R : Type*} [AddCommGroup R]
    (M : Matrix (Fin r) (Fin d) ℤ) (f : (Fin d → ℤ) →ₗ[ℤ] R)
    (hf : Function.Surjective f) (hk : LinearMap.ker f = linRelations M)
    {out : Val} (ho : TmGLQOut M out) :
    ∃ (V D : Matrix (Fin d) (Fin d) ℤ) (E : R ≃+ tmGLVec (tmGLQMod D)),
      out = .list [linVecVal (fun i => D i i),encIntMatrix V] ∧ IsUnit V.det ∧
      (∀ i, 0 < D i i) ∧ ∀ z, E (f z) = tmGLQMap V D z := by
  obtain ⟨V,D,he,hV,hpos,hD⟩ := ho
  exact ⟨V,D,linObjectPresentedFrame M f hf hk V D hV hpos hD,he,hV,hpos,
    linObjectPresentedFrame_image M f hf hk V D hV hpos hD⟩

end GI.Impl
