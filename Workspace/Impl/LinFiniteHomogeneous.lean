import Workspace.Impl.LinFiniteMatrixReduce
import Workspace.Impl.LinAffineMatrixGroup

/-! Store the full finite-abelian affine transformation as an integer
homogeneous matrix. The final row is fixed and uses modulus zero. Only
finite coordinates are reduced. -/
namespace GI.Impl
open Matrix

noncomputable def linFiniteIntMatrix {d : ℕ} (m : Fin d → ℕ)
    (f : linFiniteVec m →+ linFiniteVec m) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => (linFiniteMatrix m f i j : ℤ)

noncomputable def linFiniteHomogeneous {d : ℕ} (m : Fin d → ℕ)
    (f : linFiniteVec m →+ linFiniteVec m) (u : linFiniteVec m) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
  linAffineMatrix (linFiniteIntMatrix m f) (fun i => ((u i).val : ℤ))

def linFiniteModuli {d : ℕ} (m : Fin d → ℕ) : Fin (d + 1) → ℤ := linExtend (fun i => (m i : ℤ)) 0

theorem linFiniteIntMatrix_comp_mod {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f g : linFiniteVec m →+ linFiniteVec m) (i j : Fin d) :
    (linFiniteIntMatrix m f * linFiniteIntMatrix m g) i j % (m i : ℤ) =
      linFiniteIntMatrix m (f.comp g) i j := by
  have he := congrArg (fun n : ℕ => (n : ℤ)) (linFiniteMatrix_comp m hm f g i j)
  simp only [Int.natCast_mod, Nat.cast_sum, Nat.cast_mul] at he
  exact he.symm

theorem linFiniteIntOffset_comp_mod {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (u v : linFiniteVec m) (i : Fin d) :
    ((linFiniteIntMatrix m f).mulVec (fun j => ((v j).val : ℤ)) i + (u i).val) % (m i : ℤ) =
      ((f v i + u i).val : ℤ) := by
  have he := congrArg (fun n : ℕ => (n : ℤ)) (linFiniteAffine_comp m hm f u v i)
  simp only [Int.natCast_mod, Nat.cast_add, Nat.cast_sum, Nat.cast_mul] at he
  exact he.symm

/-- Multiplication and row reduction compute composition in the full affine
action, not only its current F_p quotient. -/
theorem linFiniteHomogeneous_comp {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f g : linFiniteVec m →+ linFiniteVec m) (u v : linFiniteVec m) :
    (fun i j => (linFiniteHomogeneous m f u * linFiniteHomogeneous m g v) i j % linFiniteModuli m i) =
      linFiniteHomogeneous m (f.comp g) (f v + u) := by
  rw [linFiniteHomogeneous, linFiniteHomogeneous, linAffineMatrix_mul]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    simp [linFiniteModuli, linFiniteHomogeneous, linAffineMatrix, linExtend]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simpa [linFiniteModuli, linFiniteHomogeneous, linAffineMatrix] using
        linFiniteIntOffset_comp_mod m hm f u v i
    | cast j =>
      simpa [linFiniteModuli, linFiniteHomogeneous, linAffineMatrix] using
        linFiniteIntMatrix_comp_mod m hm f g i j

end GI.Impl
