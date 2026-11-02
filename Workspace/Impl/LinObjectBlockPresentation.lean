import Workspace.Impl.LinObjectBlock
import Workspace.Impl.LinPresentationRows

/-! Flatten the product presentation in the exact column order used by
the matrix assembler, and append the common-translation rows. -/
namespace GI.Impl
open Matrix

def linObjectUnflatten (p d : ℕ) : (Fin (d * p) → ℤ) ≃ₗ[ℤ] (Fin p → Fin d → ℤ) where
  toFun z i j := z (finProdFinEquiv (j, i))
  invFun z k := z (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  left_inv z := by ext k; exact congrArg z (finProdFinEquiv.apply_symm_apply k)
  right_inv z := by ext i j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem linObjectBlockPresentation_ker {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i)) :
    LinearMap.ker ((linObjectProductMap B f).comp (linObjectUnflatten p d).toLinearMap) =
      linRelations (linObjectBlockMatrix M) := by
  ext z
  rw [LinearMap.mem_ker]
  change linObjectProductMap B f (linObjectUnflatten p d z) = 0 ↔ _
  rw [← LinearMap.mem_ker, linObjectProductMap_ker]
  change _ ↔ ∃ x, Matrix.vecMul x (linObjectBlockMatrix M) = z
  rw [linObjectBlockMatrix_relations]
  apply forall_congr'
  intro i
  have he : f (linObjectUnflatten p d z i) ∈ B i ↔
      linObjectUnflatten p d z i ∈ LinearMap.ker ((B i).mkQ.comp f) := by
    simp [LinearMap.mem_ker, Submodule.mkQ_apply]
  rw [he, hM]
  rfl

/-- One row for each original abelian generator, repeated across pieces. -/
def linObjectDiagonalMatrix (p d : ℕ) : Matrix (Fin d) (Fin (d * p)) ℤ :=
  fun a k => if a = (finProdFinEquiv.symm k).1 then 1 else 0

theorem linObjectDiagonalMatrix_vecMul {p d : ℕ} (z : Fin d → ℤ) :
    linObjectUnflatten p d (Matrix.vecMul z (linObjectDiagonalMatrix p d)) =
      linObjectIntegerDiagonal z := by
  ext i j
  simp [linObjectUnflatten, linObjectIntegerDiagonal, Matrix.vecMul,
    dotProduct, linObjectDiagonalMatrix, mul_ite]

theorem linObjectDiagonalMatrix_range (p d : ℕ) :
    (linRelations (linObjectDiagonalMatrix p d)).map (linObjectUnflatten p d).toLinearMap =
      LinearMap.range (linObjectIntegerDiagonal (ι := Fin p) (d := d)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (linObjectDiagonalMatrix_vecMul x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Matrix.vecMul x (linObjectDiagonalMatrix p d), ⟨x, rfl⟩,
      linObjectDiagonalMatrix_vecMul x⟩

def linObjectQuotientMatrix {p r d : ℕ} (M : Fin p → Matrix (Fin r) (Fin d) ℤ) :
    Matrix (Fin (r * p + d)) (Fin (d * p)) ℤ :=
  linRowStack (linObjectBlockMatrix M) (linObjectDiagonalMatrix p d)

theorem linObjectRowStack_injective {r s d : ℕ}
    (M : Matrix (Fin r) (Fin d) ℤ) (C : Matrix (Fin s) (Fin d) ℤ)
    (hM : Function.Injective M.mulVec) : Function.Injective (linRowStack M C).mulVec := by
  intro x y hxy
  apply hM
  ext i
  have hi := congrFun hxy (i.castAdd s)
  simpa [Matrix.mulVec, dotProduct, linRowStack] using hi

theorem linObjectQuotientMatrix_injective {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, Function.Injective (M i).mulVec) :
    Function.Injective (linObjectQuotientMatrix M).mulVec :=
  linObjectRowStack_injective _ _ (linObjectBlockMatrix_injective M hM)

theorem linObjectQuotientMatrix_ker {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i)) :
    LinearMap.ker (((LinearMap.range (linObjectDiagonal B)).mkQ.comp
      (linObjectProductMap B f)).comp (linObjectUnflatten p d).toLinearMap) =
      linRelations (linObjectQuotientMatrix M) := by
  let E := (linObjectUnflatten p d).toLinearMap
  have hE : LinearMap.range E = ⊤ := LinearMap.range_eq_top.mpr
    (linObjectUnflatten p d).surjective
  have hker : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot.mpr
    (linObjectUnflatten p d).injective
  have hdiag : (LinearMap.range (linObjectIntegerDiagonal (ι := Fin p) (d := d))).comap E =
      linRelations (linObjectDiagonalMatrix p d) := by
    rw [← linObjectDiagonalMatrix_range, Submodule.comap_map_eq, hker, sup_bot_eq]
  rw [LinearMap.ker_comp, linObjectQuotient_ker B f hf,
    Submodule.comap_sup_of_injective (linObjectUnflatten p d).injective
      (by rw [hE]; exact le_top) (by rw [hE]; exact le_top), hdiag]
  rw [← LinearMap.ker_comp, linObjectBlockPresentation_ker B f M hM]
  exact (linRelations_stack _ _).symm

/-- The explicit block-and-diagonal matrix presents exactly `W/D`. -/
noncomputable def linObjectQuotientMatrixEquiv {Q : Type*} [AddCommGroup Q] {p r d : ℕ}
    (B : Fin p → Submodule ℤ Q) (f : (Fin d → ℤ) →ₗ[ℤ] Q)
    (hf : Function.Surjective f) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, LinearMap.ker ((B i).mkQ.comp f) = linRelations (M i)) :
    ((Fin (d * p) → ℤ) ⧸ linRelations (linObjectQuotientMatrix M)) ≃ₗ[ℤ]
      ((∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) := by
  let g := ((LinearMap.range (linObjectDiagonal B)).mkQ.comp
    (linObjectProductMap B f)).comp (linObjectUnflatten p d).toLinearMap
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp
    ((linObjectProductMap_surjective B f hf).comp (linObjectUnflatten p d).surjective)
  exact (Submodule.quotEquivOfEq _ _ (linObjectQuotientMatrix_ker B f hf M hM).symm).trans
    (g.quotKerEquivOfSurjective hg)

end GI.Impl
