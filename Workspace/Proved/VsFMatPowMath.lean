import Workspace.Proved.VsFMatMath
import Workspace.Impl.VsFMatPow
import Mathlib.Data.Matrix.Mul

/-!
# List matrices as matrices over `ZMod p`

A list of rows `A` is read as the matrix `vsFMatrix p d A : Matrix (Fin d) (Fin d) (ZMod p)`,
entry `(i, j)` being `A[i][j]`. With a zero start vector the product program computes the
matrix product (`vsFMatMulL_matrix`), and the power program computes `X^p`
(`vsFMatPowL_matrix`).
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-- The matrix of a list of rows. -/
def vsFMatrix (p d : ℕ) (A : List (List ℕ)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  fun i j => vsF p (A.getD i []) j

theorem vsFMatMulL_matrix {d : ℕ} {A X : List (List ℕ)} {z : List ℕ} (hA : A.length = d)
    (hX : VsFSq p d X) (hzl : z.length = d) (hz : vsF p z = 0) :
    vsFMatrix p d (vsFMatMulL p A X z) = vsFMatrix p d A * vsFMatrix p d X := by
  ext i j
  have hi : (i : ℕ) < A.length := hA ▸ i.2
  have hrow : (vsFMatMulL p A X z).getD i [] = vsFRowMul p (A.getD i []) X z := by
    rw [List.getD_eq_getElem _ _ (by rw [vsFMatMulL, List.length_map]; exact hi),
      List.getD_eq_getElem _ _ hi]
    simp [vsFMatMulL]
  simp only [vsFMatrix, hrow, Matrix.mul_apply]
  rw [vsFMat_rowMul p _ X z (fun r hr => by rw [(hX.rows r hr).2, hzl]), hz, zero_add,
    Finset.sum_apply, hX.len]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((((A.getD i []).getD k 0 : ℕ) : ZMod p) •
    vsF p (X.getD k [])) j)]
  rfl

theorem vsFMatPowL_matrix {d : ℕ} {X : List (List ℕ)} {z : List ℕ} (hp : 0 < p)
    (hX : VsFSq p d X) (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hz : vsF p z = 0) (k : ℕ) :
    vsFMatrix p d (vsFMatPowL p X z k) = vsFMatrix p d X ^ (k + 1) := by
  induction k with
  | zero => simp [vsFMatPowL]
  | succ k ih =>
    rw [vsFMatPowL_succ, vsFMatMulL_matrix (vsFMatPowL_sq hp hX hzb hzl k).len hX hzl hz, ih,
      ← pow_succ]

/-- **The `p`-th power.** With a zero start vector, the power program's result is `X^p`. -/
theorem vsFMatPow_matrix {d : ℕ} {X : List (List ℕ)} {z : List ℕ} (hp : 0 < p)
    (hX : VsFSq p d X) (hzb : ∀ y ∈ z, y < p) (hzl : z.length = d) (hz : vsF p z = 0) :
    vsFMatrix p d (vsFMatPowL p X z (p - 1)) = vsFMatrix p d X ^ p := by
  rw [vsFMatPowL_matrix hp hX hzb hzl hz, Nat.sub_add_cancel hp]

end GI.Proved
