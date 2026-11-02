import Workspace.Impl.LinObjectBlockPresentation

/-! Read the last coefficient block of an integer solution as the common
translation. A failed row equation is exactly failure of liftability. -/
namespace GI.Impl
open Matrix

theorem linRowStack_vecMul {r s d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (C : Matrix (Fin s) (Fin d) ℤ) (z : Fin (r + s) → ℤ) :
    Matrix.vecMul z (linRowStack M C) =
      Matrix.vecMul (fun i => z (i.castAdd s)) M +
        Matrix.vecMul (fun i => z (Fin.natAdd r i)) C := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.add_apply]
  rw [Fin.sum_univ_add]
  simp [linRowStack]

theorem linObjectCorrection_rows {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (L : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (L i))
    (w : Fin (d * p) → ℤ) (z : Fin (r * p + d) → ℤ)
    (hz : Matrix.vecMul z (linObjectQuotientMatrix L) = -w) :
    ∀ i, f (linObjectUnflatten p d w i) + f (fun j => z (Fin.natAdd (r * p) j)) ∈ B i := by
  let F := (linObjectProductMap B f).comp (linObjectUnflatten p d).toLinearMap
  let localCoeffs := fun j : Fin (r * p) => z (j.castAdd d)
  let common := fun j : Fin d => z (Fin.natAdd (r * p) j)
  have hlocal : F (Matrix.vecMul localCoeffs (linObjectBlockMatrix L)) = 0 := by
    change Matrix.vecMul localCoeffs (linObjectBlockMatrix L) ∈ LinearMap.ker F
    rw [linObjectBlockPresentation_ker B f L hL]
    exact ⟨localCoeffs, rfl⟩
  have hdiag : F (Matrix.vecMul common (linObjectDiagonalMatrix p d)) =
      linObjectDiagonal B (f common) := by
    change linObjectProductMap B f
      (linObjectUnflatten p d (Matrix.vecMul common (linObjectDiagonalMatrix p d))) = _
    rw [linObjectDiagonalMatrix_vecMul]
    rfl
  unfold linObjectQuotientMatrix at hz
  rw [linRowStack_vecMul] at hz
  have hh := congrArg F hz
  change F (Matrix.vecMul localCoeffs (linObjectBlockMatrix L) +
    Matrix.vecMul common (linObjectDiagonalMatrix p d)) = F (-w) at hh
  rw [map_add, hlocal, zero_add, hdiag, map_neg] at hh
  have he : F w + linObjectDiagonal B (f common) = 0 := by rw [hh, add_neg_cancel]
  intro i
  have hi := congrFun he i
  change (B i).mkQ (f (linObjectUnflatten p d w i)) + (B i).mkQ (f common) = 0 at hi
  rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hi
  exact hi

theorem linObjectLiftable_iff {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (L : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (L i))
    (w : Fin (d * p) → ℤ) :
    (∃ z, Matrix.vecMul z (linObjectQuotientMatrix L) = -w) ↔
      ∃ a : Q, ∀ i, f (linObjectUnflatten p d w i) + a ∈ B i := by
  change -w ∈ linRelations (linObjectQuotientMatrix L) ↔ _
  rw [Submodule.neg_mem_iff]
  rw [← linObjectQuotientMatrix_ker B f hf L hL, LinearMap.mem_ker]
  exact linObjectCommonCorrection_coordinates B f (linObjectUnflatten p d w)

end GI.Impl
