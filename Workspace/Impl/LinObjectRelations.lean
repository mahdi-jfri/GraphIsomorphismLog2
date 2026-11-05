module

public import Workspace.Impl.LinObjectBlockPresentation

@[expose] public section

/-! Assemble the presentation of the object quotient from the presentation
of `A/N` and coordinate vectors of local stabilizer generators. -/
namespace GI.Impl
open Matrix

def linObjectRelationMatrix {p t s : ℕ} (M : Matrix (Fin t) (Fin t) ℤ)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) :
    Matrix (Fin ((t + s) * p + t)) (Fin (t * p)) ℤ :=
  linObjectQuotientMatrix (fun i => linRowStack M (C i))

theorem linObjectLocalRelation_ker {Q : Type*} [AddCommGroup Q] {t s : ℕ}
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Matrix (Fin s) (Fin t) ℤ) (B : Submodule ℤ Q)
    (hB : B = (linRelations C).map f) :
    LinearMap.ker (B.mkQ.comp f) = linRelations (linRowStack M C) := by
  rw [hB, linPresentationExtend_ker, linRelations_stack,
    linPresentation_ker_eq M hM f hf hrel hcard]

theorem linObjectRelationMatrix_injective {p t s : ℕ}
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) :
    Function.Injective (linObjectRelationMatrix M C).mulVec := by
  apply linObjectQuotientMatrix_injective
  intro i
  apply linObjectRowStack_injective
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hM
  rw [Matrix.mulVec_sub, hxy, sub_self]

noncomputable def linObjectRelationMatrixEquiv {Q : Type*} [AddCommGroup Q] {p t s : ℕ}
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) (B : Fin p → Submodule ℤ Q)
    (hB : ∀ i, B i = (linRelations (C i)).map f) :
    ((Fin (t * p) → ℤ) ⧸ linRelations (linObjectRelationMatrix M C)) ≃ₗ[ℤ]
      ((∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) :=
  linObjectQuotientMatrixEquiv B f hf (fun i => linRowStack M (C i))
    (fun i => linObjectLocalRelation_ker M hM f hf hrel hcard (C i) (B i) (hB i))

end GI.Impl
