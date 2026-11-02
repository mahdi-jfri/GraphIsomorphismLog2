import Workspace.Lang.Prims.LinNormal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Integer row equations used after Hermite reduction in A.20.
Rows are relations throughout. These mathematical reductions do not introduce a
linear-system oracle. Language back substitution is a separate implementation. -/
namespace GI.Impl
open Matrix

/-- Changing relation rows by a unimodular matrix preserves the integer row lattice. -/
theorem linRowEquation_iff {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ)
    (U : Matrix (Fin r) (Fin r) ℤ) (hU : IsUnit U.det) (w : Fin c → ℤ) :
    (∃ z, z ᵥ* M = w) ↔ ∃ y, y ᵥ* (U * M) = w := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ᵥ* U⁻¹, ?_⟩
    rw [vecMul_vecMul, ← Matrix.mul_assoc, U.nonsing_inv_mul hU, Matrix.one_mul]
    exact hz
  · rintro ⟨y, hy⟩
    exact ⟨y ᵥ* U, by rw [vecMul_vecMul]; exact hy⟩

/-- Explicit lift through the Hermite premultiplier. -/
theorem linRowLift {r c : ℕ} {M H : Matrix (Fin r) (Fin c) ℤ}
    {U : Matrix (Fin r) (Fin r) ℤ} (h : U * M = H)
    {y : Fin r → ℤ} {w : Fin c → ℤ} (hy : y ᵥ* H = w) :
    (y ᵥ* U) ᵥ* M = w := by
  rw [vecMul_vecMul, h, hy]

/-- A zero row of the Hermite form pulls back to an integer kernel vector. -/
theorem linHermiteKernelRow {r c : ℕ} {M H : Matrix (Fin r) (Fin c) ℤ}
    {U : Matrix (Fin r) (Fin r) ℤ} (h : U * M = H)
    (i : Fin r) (hi : ∀ j, H i j = 0) : (U i) ᵥ* M = 0 := by
  funext j
  change (U * M) i j = 0
  rw [h, hi]

/-- The rows below the square Hermite block are zero and hence give kernel vectors. -/
theorem linHermiteKernelBottom {r c : ℕ} {M H : Matrix (Fin r) (Fin c) ℤ}
    {U : Matrix (Fin r) (Fin r) ℤ} (h : U * M = H)
    (hH : GI.Cited.IsHermiteForm H) (i : Fin r) (hi : c ≤ i.val) :
    (U i) ᵥ* M = 0 :=
  linHermiteKernelRow h i (fun j => hH.1 i j (by omega))

/-- Smith multipliers give the stated coordinate change in the integer row equation. -/
theorem linSmithEquation_iff {n : ℕ} (M U V D : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (h : U * M * V = D)
    (w : Fin n → ℤ) :
    (∃ z, z ᵥ* M = w) ↔ ∃ y, y ᵥ* D = w ᵥ* V := by
  rw [linRowEquation_iff M U hU w]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← h, ← vecMul_vecMul, hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Matrix.vecMul_injective_of_isUnit (V.isUnit_iff_isUnit_det.mpr hV)
    change (y ᵥ* (U * M)) ᵥ* V = w ᵥ* V
    rw [vecMul_vecMul, h, hy]

end GI.Impl
