import Workspace.Impl.LinPresentation
import Workspace.Impl.LinChain

/-! Assemble the complete presentation from the successive cyclic relations.
The relation rows are e_i times the i-th basis vector minus the SLP coefficients. -/
namespace GI.Impl
open Matrix

/-- The rows produced in the abelian-coordinate construction. -/
def linRelationMatrix {t : ℕ} (e : Fin t → ℕ) (C : Matrix (Fin t) (Fin t) ℤ) :
    Matrix (Fin t) (Fin t) ℤ := fun i => Pi.single i (e i : ℤ) - C i

/-- An SLP in the preceding prefix uses no later coordinate. -/
def linEarlierCoefficients {t : ℕ} (C : Matrix (Fin t) (Fin t) ℤ) : Prop :=
  ∀ i j, i ≤ j → C i j = 0

theorem linRelationMatrix_diagonal {t : ℕ} (e : Fin t → ℕ)
    (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C) (i : Fin t) :
    linRelationMatrix e C i i = (e i : ℤ) := by
  simp [linRelationMatrix, hC i i le_rfl]

theorem linRelationMatrix_tri {t : ℕ} (e : Fin t → ℕ)
    (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C) :
    (linRelationMatrix e C).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  simp [linRelationMatrix, Pi.single_apply, ne_of_lt hij, ne_of_gt hij, hC i j hij.le]

theorem linRelationMatrix_det {t : ℕ} (e : Fin t → ℕ)
    (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C) :
    (linRelationMatrix e C).det = ∏ i, (e i : ℤ) := by
  rw [Matrix.det_of_lowerTriangular _ (linRelationMatrix_tri e C hC)]
  simp_rw [linRelationMatrix_diagonal e C hC]

theorem linRelationMatrix_det_ne {t : ℕ} (e : Fin t → ℕ)
    (he : ∀ i, 0 < e i) (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C) :
    (linRelationMatrix e C).det ≠ 0 := by
  rw [linRelationMatrix_det e C hC]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast (Nat.ne_of_gt (he i))

/-- Each relation row is killed by the quotient coordinate map. -/
theorem linRelationMatrix_relations {t : ℕ} {Q : Type*} [AddCommGroup Q]
    (e : Fin t → ℕ) (C : Matrix (Fin t) (Fin t) ℤ)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q)
    (hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i)) :
    linRelations (linRelationMatrix e C) ≤ LinearMap.ker f := by
  apply linRelations_le_ker
  intro i
  simp only [linRelationMatrix, map_sub, hrel, sub_self]

/-- This is the paper's counting argument with the actual assembled rows.
The map is induced by f and sends the class of z to f z. -/
noncomputable def linCyclicPresentationEquiv {t : ℕ} {Q : Type*} [AddCommGroup Q]
    (e : Fin t → ℕ) (he : ∀ i, 0 < e i)
    (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i))
    (hcard : Nat.card Q = ∏ i, e i) :
    ((Fin t → ℤ) ⧸ linRelations (linRelationMatrix e C)) ≃ₗ[ℤ] Q :=
  linPresentationEquiv _ (linRelationMatrix_det_ne e he C hC) f hf
    (linRelationMatrix_relations e C f hrel) (by
      rw [linRelationMatrix_det e C hC, ← Int.natAbsHom_apply, map_prod]
      simpa using hcard)

@[simp] theorem linCyclicPresentationEquiv_mk {t : ℕ} {Q : Type*} [AddCommGroup Q]
    (e : Fin t → ℕ) (he : ∀ i, 0 < e i)
    (C : Matrix (Fin t) (Fin t) ℤ) (hC : linEarlierCoefficients C)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : ∀ i, f (Pi.single i (e i : ℤ)) = f (C i))
    (hcard : Nat.card Q = ∏ i, e i) (z : Fin t → ℤ) :
    linCyclicPresentationEquiv e he C hC f hf hrel hcard
      ((linRelations (linRelationMatrix e C)).mkQ z) = f z := rfl

end GI.Impl
