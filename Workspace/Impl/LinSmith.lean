module

public import Workspace.Impl.LinSolve

@[expose] public section

/-! Relation tests and explicit integer lifts from the Smith multipliers.
The invariant factors are the positive diagonal entries, with the divisibility
ordering already certified by IsSmithForm. -/
namespace GI.Impl
open Matrix GI.Cited

/-- A square Smith output is a diagonal matrix. -/
theorem linSmithDiagonal {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : IsSmithForm D) :
    D = Matrix.diagonal (fun i => D i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact hD.1 i j (fun h => hij (Fin.ext h))

/-- Every pivot of a nonsingular square Smith form is positive. -/
theorem linSmithDiagonal_pos {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ)
    (hD : IsSmithForm D) (hdet : D.det ≠ 0) (i : Fin n) : 0 < D i i := by
  have hd : ∏ i, D i i ≠ 0 := by
    rwa [linSmithDiagonal D hD, Matrix.det_diagonal] at hdet
  have hn : D i i ≠ 0 := Finset.prod_ne_zero_iff.mp hd i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hD.2.1 i i rfl) (Ne.symm hn)

/-- A diagonal integer row equation has a solution exactly when each pivot divides
its corresponding target coordinate. -/
theorem linSmithDiagonal_solvable {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ)
    (hD : IsSmithForm D) (w : Fin n → ℤ) :
    (∃ y, y ᵥ* D = w) ↔ ∀ i, D i i ∣ w i := by
  rw [linSmithDiagonal D hD]
  simp only [Matrix.diagonal_apply_eq]
  constructor
  · rintro ⟨y, hy⟩ i
    have hi := congrFun hy i
    rw [Matrix.vecMul_diagonal] at hi
    exact ⟨y i, by rw [mul_comm]; exact hi.symm⟩
  · intro hw
    refine ⟨fun i => w i / D i i, ?_⟩
    funext i
    rw [Matrix.vecMul_diagonal]
    exact Int.ediv_mul_cancel (hw i)

/-- Relation testing in the original coordinates after the Smith coordinate change. -/
theorem linSmithRelation {n : ℕ} (M U V D : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (h : U * M * V = D)
    (hD : IsSmithForm D) (w : Fin n → ℤ) :
    (∃ z, z ᵥ* M = w) ↔ ∀ i, D i i ∣ (w ᵥ* V) i := by
  rw [linSmithEquation_iff M U V D hU hV h w, linSmithDiagonal_solvable D hD]

/-- The quotient-pivot coefficients, pulled back through the row multiplier U. -/
def linSmithLift {n : ℕ} (U V D : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ) : Fin n → ℤ :=
  (fun i => (w ᵥ* V) i / D i i) ᵥ* U

/-- The explicit lift solves the original integer equation whenever the relation test succeeds. -/
theorem linSmithLift_spec {n : ℕ} (M U V D : Matrix (Fin n) (Fin n) ℤ)
    (hV : IsUnit V.det) (h : U * M * V = D) (hD : IsSmithForm D)
    (w : Fin n → ℤ) (hw : ∀ i, D i i ∣ (w ᵥ* V) i) :
    linSmithLift U V D w ᵥ* M = w := by
  apply Matrix.vecMul_injective_of_isUnit (V.isUnit_iff_isUnit_det.mpr hV)
  change (linSmithLift U V D w ᵥ* M) ᵥ* V = w ᵥ* V
  rw [linSmithLift, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, h, linSmithDiagonal D hD]
  funext i
  rw [Matrix.vecMul_diagonal]
  simpa only [Matrix.diagonal_apply_eq] using Int.ediv_mul_cancel (hw i)

end GI.Impl
