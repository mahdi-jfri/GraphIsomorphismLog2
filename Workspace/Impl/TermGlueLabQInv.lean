module

public import Workspace.Cited.AlgoTerminal
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# The inverse of a unimodular matrix from its Hermite form

Step 5 of the label program. The quotient program returns `[d, V]` with `V`
unimodular, and the matrix of the linear part in the coordinates `x ↦ x V mod d` is
`V⁻¹ C V`. The inverse comes from one Hermite call: `U V = H` with `H` in Hermite form and `U`
unimodular. Since `det H = det U det V` is a unit and `H` is upper triangular with a positive
diagonal, every diagonal entry is `1`; the entries above the diagonal lie in `[0, 1)`, so
`H = 1` (`tmGLQ_hermite_unimod`) and `U V = 1`, hence `V U = 1` (`tmGLQ_inv_of_hermite`).
-/

namespace GI.Impl

open GI.Cited Matrix

/-- **A Hermite form with unit determinant is the identity.** -/
theorem tmGLQ_hermite_unimod {t : ℕ} {H : Matrix (Fin t) (Fin t) ℤ} (hH : IsHermiteForm H)
    (hdet : IsUnit H.det) : H = 1 := by
  obtain ⟨hlow, hdiag, hup⟩ := hH
  have htri : H.BlockTriangular id := fun i j hji => hlow i j hji
  have hd : H.det = ∏ i, H i i := Matrix.det_of_upperTriangular htri
  have hpos : ∀ i, 0 < H i i := fun i => hdiag i i rfl
  -- the product of the positive diagonal entries is a unit, hence `1`
  have hprod : ∏ i, H i i = 1 := by
    rcases Int.isUnit_iff.mp (hd ▸ hdet) with h | h
    · exact h
    · have : 0 < ∏ i, H i i := Finset.prod_pos fun i _ => hpos i
      omega
  have hone : ∀ i, H i i = 1 := by
    intro i
    have hdv : H i i ∣ 1 := hprod ▸ Finset.dvd_prod_of_mem (fun j => H j j) (Finset.mem_univ i)
    exact Int.eq_one_of_dvd_one (hpos i).le hdv
  ext i j
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · rw [hlow i j h, Matrix.one_apply_ne (fun e => by rw [e] at h; exact lt_irrefl _ h)]
  · have e : i = j := Fin.ext h.symm
    subst e; rw [hone, Matrix.one_apply_eq]
  · obtain ⟨h1, h2⟩ := hup i j j h rfl
    rw [hone j] at h2
    rw [Matrix.one_apply_ne (fun e => by rw [e] at h; exact lt_irrefl _ h)]
    omega

/-- **The Hermite multiplier of a unimodular matrix is its inverse.** -/
theorem tmGLQ_inv_of_hermite {t : ℕ} {U V H : Matrix (Fin t) (Fin t) ℤ} (hU : IsUnit U.det)
    (hV : IsUnit V.det) (hUV : U * V = H) (hH : IsHermiteForm H) : U * V = 1 ∧ V * U = 1 := by
  have hdet : IsUnit H.det := by rw [← hUV, Matrix.det_mul]; exact hU.mul hV
  have h1 : U * V = 1 := hUV.trans (tmGLQ_hermite_unimod hH hdet)
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

end GI.Impl
