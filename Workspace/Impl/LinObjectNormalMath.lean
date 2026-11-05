module

public import Workspace.Impl.LinObjectRelations
public import Workspace.Impl.TermGlueLabQMath

@[expose] public section

/-! The Hermite–Smith output supplies finite coordinates for the exact
object quotient, with the coordinate map specified on integer vectors. -/
namespace GI.Impl
open GI.Cited Matrix

def linObjectFullRankInst {p t s : ℕ} (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) (hpos : 0 < t * p) : FullRankInst where
  r := (t + s) * p + t
  c := t * p
  c_pos := hpos
  c_le := by nlinarith
  A := linObjectRelationMatrix M C
  rank := linObjectRelationMatrix_injective M hM C

variable {Q : Type*} [AddCommGroup Q] {p t s : ℕ}

@[simp] theorem linObjectRelationMatrixEquiv_mk
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) (B : Fin p → Submodule ℤ Q)
    (hB : ∀ i, B i = (linRelations (C i)).map f) (z : Fin (t * p) → ℤ) :
    linObjectRelationMatrixEquiv M hM f hf hrel hcard C B hB
      ((linRelations (linObjectRelationMatrix M C)).mkQ z) =
      (LinearMap.range (linObjectDiagonal B)).mkQ
        (linObjectProductMap B f (linObjectUnflatten p t z)) := rfl

noncomputable def linObjectNormalEquiv
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) (B : Fin p → Submodule ℤ Q)
    (hB : ∀ i, B i = (linRelations (C i)).map f)
    (V D : Matrix (Fin (t * p)) (Fin (t * p)) ℤ) (hV : IsUnit V.det)
    (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z (linObjectRelationMatrix M C) = x) ↔
      ∀ i, D i i ∣ (Matrix.vecMul x V) i) :
    ((∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) ≃+ tmGLVec (tmGLQMod D) :=
  (linObjectRelationMatrixEquiv M hM f hf hrel hcard C B hB).symm.toAddEquiv.trans
    (tmGLQOutEquiv hV hpos hD)

theorem linObjectNormalEquiv_mk
    (M : Matrix (Fin t) (Fin t) ℤ) (hM : M.det ≠ 0)
    (f : (Fin t → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Fin p → Matrix (Fin s) (Fin t) ℤ) (B : Fin p → Submodule ℤ Q)
    (hB : ∀ i, B i = (linRelations (C i)).map f)
    (V D : Matrix (Fin (t * p)) (Fin (t * p)) ℤ) (hV : IsUnit V.det)
    (hpos : ∀ i, 0 < D i i)
    (hD : ∀ x, (∃ z, Matrix.vecMul z (linObjectRelationMatrix M C) = x) ↔
      ∀ i, D i i ∣ (Matrix.vecMul x V) i) (z : Fin (t * p) → ℤ) :
    linObjectNormalEquiv M hM f hf hrel hcard C B hB V D hV hpos hD
      ((LinearMap.range (linObjectDiagonal B)).mkQ
        (linObjectProductMap B f (linObjectUnflatten p t z))) = tmGLQMap V D z := by
  rw [← linObjectRelationMatrixEquiv_mk M hM f hf hrel hcard C B hB z]
  change tmGLQOutEquiv hV hpos hD
    ((linObjectRelationMatrixEquiv M hM f hf hrel hcard C B hB).symm
      (linObjectRelationMatrixEquiv M hM f hf hrel hcard C B hB
        ((linRelations (linObjectRelationMatrix M C)).mkQ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact tmGLQOutEquiv_mk hV hpos hD z

end GI.Impl
