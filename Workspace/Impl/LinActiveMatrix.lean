module

public import Workspace.Impl.LinPrimaryMatrixAlgebra

@[expose] public section

/-! Extend a representation on retained coordinates by the trivial action on
the other coordinates. This avoids changing matrix dimensions between layers. -/
namespace GI.Impl
open scoped BigOperators
variable {R : Type*} [CommRing R] {d : ℕ}

def linActiveMatrix (active : Fin d → Prop) [DecidablePred active]
    (A : Matrix (Fin d) (Fin d) R) : Matrix (Fin d) (Fin d) R := fun i j =>
  if active i then if active j then A i j else 0 else if i = j then 1 else 0

theorem linActiveMatrix_congr (active : Fin d → Prop) [DecidablePred active]
    (A B : Matrix (Fin d) (Fin d) R) (h : ∀ i j, active i → A i j = B i j) :
    linActiveMatrix active A = linActiveMatrix active B := by
  funext i j
  by_cases hi : active i <;> by_cases hj : active j <;> simp [linActiveMatrix, hi, hj, h i j]

@[simp] theorem linActiveMatrix_one (active : Fin d → Prop) [DecidablePred active] :
    linActiveMatrix active (1 : Matrix (Fin d) (Fin d) R) = 1 := by
  ext i j
  by_cases hi : active i <;> by_cases hj : active j <;>
    by_cases hij : i = j <;> simp_all [linActiveMatrix, Matrix.one_apply]

/-- Discarded columns contribute zero to retained rows. This is the precise
condition supplied by compatibility of the finite-abelian coordinate orders. -/
theorem linActiveMatrix_mul (active : Fin d → Prop) [DecidablePred active]
    (A B : Matrix (Fin d) (Fin d) R)
    (hdrop : ∀ i j, active i → ¬active j → A i j = 0) :
    linActiveMatrix active (A * B) = linActiveMatrix active A * linActiveMatrix active B := by
  ext i j
  by_cases hi : active i
  · by_cases hj : active j
    · simp only [linActiveMatrix, hi, hj, if_pos, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : active k
      · simp [linActiveMatrix, hi, hj, hk]
      · simp [linActiveMatrix, hi, hj, hk, hdrop i k hi hk]
    · simp only [linActiveMatrix, hi, hj, if_pos, if_neg, Matrix.mul_apply]
      symm
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : active k <;> simp [linActiveMatrix, hi, hj, hk]
  · have hrow (k : Fin d) : linActiveMatrix active A i k =
        (1 : Matrix (Fin d) (Fin d) R) i k := by simp [linActiveMatrix, hi, Matrix.one_apply]
    calc linActiveMatrix active (A * B) i j = linActiveMatrix active B i j := by
            simp [linActiveMatrix, hi]
      _ = ((1 : Matrix (Fin d) (Fin d) R) * linActiveMatrix active B) i j := by rw [Matrix.one_mul]
      _ = (linActiveMatrix active A * linActiveMatrix active B) i j := by
            simp only [Matrix.mul_apply, hrow]

end GI.Impl
