module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section

/-!
# Bordered determinants

Two determinant identities for matrices bordered by one or two extra rows and columns. They
are the algebra behind Bareiss elimination (`Workspace/Proved/HNFBareiss.lean`).

* `hnfBorder1`: for `N = [[A, b], [ρ, a]]` with `A` square and `det A ≠ 0`,
  `det N = a · det A - ρ · adj A · b` (over `ℤ`).
* `hnfSylvester`: for `N` with a `2 × 2` corner, `det A · det N` equals the `2 × 2`
  determinant of the four one-row borders of `A` (Sylvester's identity).

Both come from Mathlib's Schur complement formula `Matrix.det_fromBlocks₁₁`.
-/

namespace GI.Proved

open Matrix

section Field

variable {F : Type*} [Field F] {n : ℕ}

/-- The one-row borders of the top-left block of `N`: rows `inl ·` and `inr a`, columns
`inl ·` and `inr b`. -/
def hnfSub2 {α : Type*} (N : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) α) (a b : Fin 2) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) α :=
  N.submatrix (Sum.map id fun _ => a) (Sum.map id fun _ => b)

/-- A one-row border is `det A` times one entry of the Schur complement. -/
theorem hnfSub2_det (N : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) F) [Invertible N.toBlocks₁₁]
    (a b : Fin 2) :
    (hnfSub2 N a b).det = N.toBlocks₁₁.det *
      (N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂) a b := by
  have e : hnfSub2 N a b = fromBlocks N.toBlocks₁₁ (N.toBlocks₁₂.submatrix id fun _ => b)
      (N.toBlocks₂₁.submatrix (fun _ => a) id) (N.toBlocks₂₂.submatrix (fun _ => a) fun _ => b) := by
    ext (i | i) (j | j) <;> rfl
  rw [e, det_fromBlocks₁₁, Matrix.det_fin_one]
  simp [Matrix.sub_apply, Matrix.mul_apply, toBlocks₂₂, toBlocks₂₁, toBlocks₁₂]

/-- **Sylvester's identity** for a two-row border. -/
theorem hnfSylvester (N : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) F)
    (hA : N.toBlocks₁₁.det ≠ 0) :
    N.toBlocks₁₁.det * N.det = (hnfSub2 N 0 0).det * (hnfSub2 N 1 1).det -
      (hnfSub2 N 1 0).det * (hnfSub2 N 0 1).det := by
  haveI : Invertible N.toBlocks₁₁ := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA)
  rw [hnfSub2_det, hnfSub2_det, hnfSub2_det, hnfSub2_det]
  have h := det_fromBlocks₁₁ N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂
  rw [fromBlocks_toBlocks] at h
  rw [h, Matrix.det_fin_two]
  ring

end Field

/-- One-row border over a field: `det [[A, B], [C, D]] = D · det A - C · adj A · B`. -/
theorem hnfBorder1F {F : Type*} [Field F] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m F) (B : Matrix m (Fin 1) F) (C : Matrix (Fin 1) m F)
    (D : Matrix (Fin 1) (Fin 1) F) (hA : A.det ≠ 0) :
    (fromBlocks A B C D).det = D 0 0 * A.det - (C * A.adjugate * B) 0 0 := by
  haveI : Invertible A := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hA)
  rw [det_fromBlocks₁₁, Matrix.det_fin_one, invOf_eq_nonsing_inv, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.sub_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul]
  field_simp

/-- **One-row border over `ℤ`.** For `N = [[A, b], [ρ, a]]` with `det A ≠ 0`,
`det N = a · det A - ρ · adj A · b`. -/
theorem hnfBorder1 {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℤ) (B : Matrix m (Fin 1) ℤ) (C : Matrix (Fin 1) m ℤ)
    (D : Matrix (Fin 1) (Fin 1) ℤ) (hA : A.det ≠ 0) :
    (fromBlocks A B C D).det = D 0 0 * A.det - (C * A.adjugate * B) 0 0 := by
  apply Int.cast_injective (α := ℚ)
  have hA' : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hA
  have h := hnfBorder1F (A.map (Int.cast : ℤ → ℚ)) (B.map Int.cast) (C.map Int.cast)
    (D.map Int.cast) hA'
  rw [← fromBlocks_map, ← Int.cast_det, ← Int.cast_det] at h
  have hadj : (A.map (Int.cast : ℤ → ℚ)).adjugate = A.adjugate.map Int.cast :=
    (RingHom.map_adjugate (Int.castRingHom ℚ) A).symm
  rw [hadj] at h
  rw [h]
  simp [Matrix.mul_apply]

/-- **Sylvester's identity over `ℤ`.** -/
theorem hnfSylvesterZ {n : ℕ} (N : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) ℤ)
    (hA : N.toBlocks₁₁.det ≠ 0) :
    N.toBlocks₁₁.det * N.det = (hnfSub2 N 0 0).det * (hnfSub2 N 1 1).det -
      (hnfSub2 N 1 0).det * (hnfSub2 N 0 1).det := by
  apply Int.cast_injective (α := ℚ)
  have hA' : (N.map (Int.cast : ℤ → ℚ)).toBlocks₁₁.det ≠ 0 := by
    change (N.toBlocks₁₁.map (Int.cast : ℤ → ℚ)).det ≠ 0
    rw [← Int.cast_det]; exact_mod_cast hA
  have h := hnfSylvester (N.map (Int.cast : ℤ → ℚ)) hA'
  have e : ∀ a b : Fin 2, hnfSub2 (N.map (Int.cast : ℤ → ℚ)) a b = (hnfSub2 N a b).map Int.cast :=
    fun _ _ => rfl
  rw [e, e, e, e, ← Int.cast_det, ← Int.cast_det, ← Int.cast_det, ← Int.cast_det,
    show (N.map (Int.cast : ℤ → ℚ)).toBlocks₁₁ = N.toBlocks₁₁.map Int.cast from rfl,
    ← Int.cast_det, ← Int.cast_det] at h
  simpa only [Int.cast_mul, Int.cast_sub] using h

end GI.Proved
