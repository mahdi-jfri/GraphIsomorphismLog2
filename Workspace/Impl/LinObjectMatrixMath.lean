import Workspace.Impl.LinObjectAffineMatrix
import Workspace.Impl.LinAffineFromAction

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectFiniteZero_cast {d : ℕ} (m : Fin d → ℕ) :
    (fun i => (((0 : Fin d → ℤ) i) : ZMod (m i))) = (0 : linFiniteVec m) := by
  funext i
  simp

theorem linObjectFiniteBasis_cast {d : ℕ} (m : Fin d → ℕ) (j : Fin d) :
    (fun i => (((Pi.single j (1 : ℤ) : Fin d → ℤ) i : ℤ) : ZMod (m i))) = Pi.single j 1 := by
  classical
  funext i
  by_cases hi : i = j
  · subst i; simp
  · simp [Pi.single_eq_of_ne hi]

/-- Basis evaluations minus the translation are precisely the columns
in the finite-affine caller's convention, including modulus-one factors. -/
theorem linObjectAffineMatrix_columns {G : Type*} [Group G] {d : ℕ}
    (m : Fin d → ℕ) (F : G →* Equiv.Perm (linFiniteVec m))
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) :
    tmGLMat m (linActionLinearRep F hF g).toAddMonoidHom =
      fun i j => (((F g (Pi.single j 1) - F g 0) i).val : ℤ) := rfl

/-- Transposition changes the runtime list of columns into the matrix
expected by `tmGLAffItem`. -/
theorem linObjectAffineMatrix_transpose {G : Type*} [Group G] {d : ℕ}
    (m : Fin d → ℕ) (F : G →* Equiv.Perm (linFiniteVec m))
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) :
    Matrix.transpose (fun j i => (((F g (Pi.single j 1) - F g 0) i).val : ℤ)) =
      tmGLMat m (linActionLinearRep F hF g).toAddMonoidHom := rfl

end GI.Impl
