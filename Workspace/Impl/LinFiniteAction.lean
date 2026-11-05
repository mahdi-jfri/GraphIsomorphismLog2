module

public import Workspace.Impl.LinFiniteHomogeneous
public import Workspace.Impl.AddEquivGroup

@[expose] public section

/-! The full affine data attached to a cover element and its inverse.
Its group law is matrix multiplication followed by finite-coordinate reduction. -/
namespace GI.Impl
open GI.Cited GI.Lang

variable {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)

def linFiniteActionLinear (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (g : G) :
    linFiniteVec m →+ linFiniteVec m := (ρ g).toAddMonoidHom

noncomputable def linFiniteActionMatrix (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (g : G) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
  linFiniteHomogeneous m (linFiniteActionLinear m ρ g) (c g)

noncomputable def linFiniteAffineVal (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (g : G) : Val :=
  .list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteActionMatrix m ρ c g),
    encIntMatrix (linFiniteActionMatrix m ρ c g⁻¹)]

/-- Matrix multiplication computes the full action of the cover product. -/
theorem linFiniteActionMatrix_mul (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    (fun i j => (linFiniteActionMatrix m ρ c g * linFiniteActionMatrix m ρ c h) i j % linFiniteModuli m i) =
      linFiniteActionMatrix m ρ c (g * h) := by
  have he : (linFiniteActionLinear m ρ g).comp (linFiniteActionLinear m ρ h) =
      linFiniteActionLinear m ρ (g * h) := by
    ext x i
    simp [linFiniteActionLinear, map_mul]
  unfold linFiniteActionMatrix
  rw [linFiniteHomogeneous_comp m hm, he]
  have hh : linFiniteActionLinear m ρ g (c h) + c g = c (g * h) := (hc g h).symm
  rw [hh]

/-- Inversion just exchanges the retained forward and inverse actions. -/
theorem linFiniteAffineVal_inv (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (g : G) :
    linFiniteAffineVal m ρ c g⁻¹ =
      .list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteActionMatrix m ρ c g⁻¹),
        encIntMatrix (linFiniteActionMatrix m ρ c g)] := by
  simp only [linFiniteAffineVal, inv_inv]

end GI.Impl
