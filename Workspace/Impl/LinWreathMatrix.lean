import Workspace.Impl.LinWreathGroup
import Workspace.Impl.LinAffineMatrixGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The two-copy representation on numbered dense coordinates. The permutation
cover and the vector space use the same first-copy, second-copy convention. -/
namespace GI.Impl
open Equiv
variable {R : Type*} [CommRing R] {d : ℕ}

/-- Matrices act on column vectors in the standard basis. -/
def linMatrixLinearEquiv : Matrix.GeneralLinearGroup (Fin d) R ≃*
    ((Fin d → R) ≃ₗ[R] (Fin d → R)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin d → R))

@[simp] theorem linMatrixLinearEquiv_apply
    (A : Matrix.GeneralLinearGroup (Fin d) R) (x : Fin d → R) :
    linMatrixLinearEquiv A x = A.val.mulVec x := rfl

/-- Flatten the two vector copies by the numbering of the permutation cover. -/
def linWreathNumberLinear : (linTwo → Fin d → R) ≃ₗ[R] (Fin (d + d) → R) where
  toFun x i := x ((linWreathNumber d).symm i).2 ((linWreathNumber d).symm i).1
  invFun x q i := x (linWreathNumber d (i, q))
  left_inv x := by funext q i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linWreathNumberLinear_apply (x : linTwo → Fin d → R)
    (i : Fin d) (q : linTwo) :
    linWreathNumberLinear x (linWreathNumber d (i, q)) = x q i := by
  simp [linWreathNumberLinear]

@[simp] theorem linWreathNumberLinear_symm_apply (x : Fin (d + d) → R)
    (i : Fin d) (q : linTwo) :
    linWreathNumberLinear.symm x q i = x (linWreathNumber d (i, q)) := rfl

variable {H : Type*} [Group H]

/-- Move the wreath representation to numbered coordinates. -/
def linWreathNumberRep (ρ : H →* ((Fin d → R) ≃ₗ[R] (Fin d → R))) :
    (H ≀ᵣ linTwo) →* ((Fin (d + d) → R) ≃ₗ[R] (Fin (d + d) → R)) where
  toFun a := linWreathNumberLinear.symm.trans ((linWreathRep ρ a).trans linWreathNumberLinear)
  map_one' := by ext x i; simp
  map_mul' a b := by ext x i; simp

@[simp] theorem linWreathNumberRep_apply
    (ρ : H →* ((Fin d → R) ≃ₗ[R] (Fin d → R))) (a : H ≀ᵣ linTwo)
    (x : Fin (d + d) → R) (i : Fin d) (q : linTwo) :
    linWreathNumberRep ρ a x (linWreathNumber d (i, q)) =
      ρ (a.left q) (fun j => x (linWreathNumber d (j, a.right⁻¹ * q))) i := by
  simp [linWreathNumberRep, linWreathNumberLinear]

/-- The actual dense invertible matrices supplied to VectorStabilizer. -/
def linWreathMatrixRep (φ : H →* Matrix.GeneralLinearGroup (Fin d) R) :
    (H ≀ᵣ linTwo) →* Matrix.GeneralLinearGroup (Fin (d + d)) R :=
  linMatrixLinearEquiv.symm.toMonoidHom.comp
    (linWreathNumberRep (linMatrixLinearEquiv.toMonoidHom.comp φ))

@[simp] theorem linWreathMatrixRep_mulVec
    (φ : H →* Matrix.GeneralLinearGroup (Fin d) R) (a : H ≀ᵣ linTwo)
    (x : Fin (d + d) → R) :
    (linWreathMatrixRep φ a).val.mulVec x =
      linWreathNumberRep (linMatrixLinearEquiv.toMonoidHom.comp φ) a x := by
  change linMatrixLinearEquiv (linMatrixLinearEquiv.symm _) x = _
  rw [MulEquiv.apply_symm_apply]

/-- On a numbered pair of vectors, the matrix stabilizer is precisely the
abstract wreath stabilizer used in the transport reduction. -/
theorem linWreathMatrixRep_fixed
    (φ : H →* Matrix.GeneralLinearGroup (Fin d) R) (a : H ≀ᵣ linTwo)
    (v w : Fin d → R) :
    (linWreathMatrixRep φ a).val.mulVec (linWreathNumberLinear (linWreathPair v w)) =
        linWreathNumberLinear (linWreathPair v w) ↔
      linWreathRep (R := R) (linMatrixLinearEquiv.toMonoidHom.comp φ) a (linWreathPair v w) =
        linWreathPair v w := by
  rw [linWreathMatrixRep_mulVec]
  let e := linWreathNumberLinear (R := R) (d := d)
  change e (linWreathRep (R := R) (linMatrixLinearEquiv.toMonoidHom.comp φ) a
    (e.symm (e (linWreathPair v w)))) = e (linWreathPair v w) ↔ _
  rw [LinearEquiv.symm_apply_apply, e.injective.eq_iff]

/-- Reading one column of the numbered wreath matrix gives either one old
matrix column or zero, according to the copy permutation. -/
theorem linWreathMatrixRep_entry
    (φ : H →* Matrix.GeneralLinearGroup (Fin d) R) (a : H ≀ᵣ linTwo)
    (i j : Fin d) (q r : linTwo) :
    (linWreathMatrixRep φ a).val (linWreathNumber d (i, q)) (linWreathNumber d (j, r)) =
      if r = a.right⁻¹ * q then (φ (a.left q)).val i j else 0 := by
  classical
  have hs : (fun k : Fin d =>
      (Pi.single (linWreathNumber d (j, r)) (1 : R) : Fin (d + d) → R)
        (linWreathNumber d (k, a.right⁻¹ * q))) =
      if r = a.right⁻¹ * q then Pi.single j 1 else 0 := by
    ext k
    by_cases hr : r = a.right⁻¹ * q
    · subst r
      simp [Pi.single_apply, (linWreathNumber d).injective.eq_iff, eq_comm]
    · have he : linWreathNumber d (k, a.right⁻¹ * q) ≠ linWreathNumber d (j, r) := by
        intro hh
        have := congrArg Prod.snd ((linWreathNumber d).injective hh)
        exact hr this.symm
      simp [Pi.single_apply, he, Ne.symm he, hr]
  have hh := congrFun (linWreathMatrixRep_mulVec φ a
    (Pi.single (linWreathNumber d (j, r)) (1 : R) : Fin (d + d) → R)) (linWreathNumber d (i, q))
  rw [Matrix.mulVec_single_one, linWreathNumberRep_apply] at hh
  change (linWreathMatrixRep φ a).val (linWreathNumber d (i, q)) (linWreathNumber d (j, r)) =
    ((φ (a.left q)).val.mulVec (fun k =>
      (Pi.single (linWreathNumber d (j, r)) (1 : R) : Fin (d + d) → R)
        (linWreathNumber d (k, a.right⁻¹ * q)))) i at hh
  rw [hs] at hh
  split_ifs at hh ⊢ <;> simpa [Matrix.mulVec_single_one] using hh

end GI.Impl
