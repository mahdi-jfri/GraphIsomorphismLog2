import Workspace.CartesianConstruct

namespace GI.CartesianCover

variable {I D : Type*}

/-- A permutation preserving one coordinate's fibers induces a genuine
permutation of that coordinate. The inverse is derived from its actual inverse. -/
def coordinateFromFibers (h : Equiv.Perm (I → D)) (i : I)
    (forward : ∀ x y : I → D, x i = y i → h x i = h y i)
    (backward : ∀ x y : I → D, x i = y i → h.symm x i = h.symm y i) : Equiv.Perm D where
  toFun d := h (fun _ => d) i
  invFun d := h.symm (fun _ => d) i
  left_inv d := by
    calc
      h.symm (fun _ => h (fun _ => d) i) i = h.symm (h (fun _ => d)) i := backward _ _ rfl
      _ = d := by rw [h.symm_apply_apply]
  right_inv d := by
    calc
      h (fun _ => h.symm (fun _ => d) i) i = h (h.symm (fun _ => d)) i := forward _ _ rfl
      _ = d := by rw [h.apply_symm_apply]

theorem coordinateFromFibers_apply (h : Equiv.Perm (I → D)) (i : I)
    (forward : ∀ x y : I → D, x i = y i → h x i = h y i)
    (backward : ∀ x y : I → D, x i = y i → h.symm x i = h.symm y i)
    (x : I → D) : coordinateFromFibers h i forward backward (x i) = h x i :=
  forward _ _ rfl

variable {H : Subgroup (Equiv.Perm (I → D))}

/-- The component permutations and their homomorphism laws are constructed
from the actual coordinate-stabilizer action; they are not supplied as data. -/
def ofStabilizerFiberInvariance (positions : H →* Equiv.Perm I)
    (fibers : ∀ (i : I) (h : coordinateStabilizer positions i) (x y : I → D),
      x i = y i → ((h.val : Equiv.Perm (I → D)) x) i =
        ((h.val : Equiv.Perm (I → D)) y) i) : CartesianCover H :=
  ofPermutations positions
    (fun i h => coordinateFromFibers h.val.val i (fibers i h) (fibers i h⁻¹))
    (fun i h x => coordinateFromFibers_apply h.val.val i (fibers i h) (fibers i h⁻¹) x)

/-- The usual transported fiber-preservation law yields the complete
CartesianCover consumed by the proved budget theorem. -/
def ofFiberInvariance (positions : H →* Equiv.Perm I)
    (fibers : ∀ (h : H) (i : I) (x y : I → D), x i = y i →
      ((h : Equiv.Perm (I → D)) x) (positions h i) =
        ((h : Equiv.Perm (I → D)) y) (positions h i)) : CartesianCover H :=
  ofStabilizerFiberInvariance positions (by
    intro i h x y he
    have hi : positions h.val i = i := h.property
    simpa only [hi] using fibers h.val i x y he)

theorem ofFiberInvariance_positions (positions : H →* Equiv.Perm I)
    (fibers : ∀ (h : H) (i : I) (x y : I → D), x i = y i →
      ((h : Equiv.Perm (I → D)) x) (positions h i) =
        ((h : Equiv.Perm (I → D)) y) (positions h i)) :
    (ofFiberInvariance positions fibers).positions = positions := rfl

end GI.CartesianCover

#print axioms GI.CartesianCover.coordinateFromFibers
#print axioms GI.CartesianCover.coordinateFromFibers_apply
#print axioms GI.CartesianCover.ofStabilizerFiberInvariance
#print axioms GI.CartesianCover.ofFiberInvariance
#print axioms GI.CartesianCover.ofFiberInvariance_positions
