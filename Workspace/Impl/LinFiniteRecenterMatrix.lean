module

public import Workspace.Impl.LinFiniteRecenter
public import Workspace.Impl.LinFiniteHomogeneous

@[expose] public section

namespace GI.Impl
open scoped BigOperators

theorem linFiniteIntMatrix_apply_cast {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (w : linFiniteVec m) (i : Fin d) :
    (((linFiniteIntMatrix m f).mulVec (fun j => ((w j).val : ℤ)) i : ℤ) : ZMod (m i)) = f w i := by
  rw [linFiniteMatrix_apply m hm f w i]
  simp only [Matrix.mulVec, dotProduct, linFiniteIntMatrix, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Nat.cast_sum, Nat.cast_mul]

theorem linFiniteRecenter_cast {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (w : linFiniteVec m) (g : G) :
    (fun i => (((linFiniteIntMatrix m (ρ g).toAddMonoidHom).mulVec (fun j => ((w j).val : ℤ)) i +
      ((c g i).val : ℤ) - ((w i).val : ℤ) : ℤ) : ZMod (m i))) = linFiniteRecenter ρ c w g := by
  funext i
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  simp only [Int.cast_sub, Int.cast_add, linFiniteIntMatrix_apply_cast m hm,
    Int.cast_natCast, ZMod.natCast_zmod_val, linFiniteRecenter, Pi.sub_apply, Pi.add_apply]
  rfl

theorem linFiniteRecenter_val {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (w : linFiniteVec m) (g : G) (i : Fin d) :
    ((linFiniteRecenter ρ c w g i).val : ℤ) =
      ((linFiniteIntMatrix m (ρ g).toAddMonoidHom).mulVec (fun j => ((w j).val : ℤ)) i +
        ((c g i).val : ℤ) - ((w i).val : ℤ)) % (m i : ℤ) := by
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  have he := congrFun (linFiniteRecenter_cast m hm ρ c w g) i
  rw [← he]
  exact ZMod.val_intCast _

end GI.Impl
