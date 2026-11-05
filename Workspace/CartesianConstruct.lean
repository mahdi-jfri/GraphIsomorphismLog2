module

public import Workspace.CartesianCover

@[expose] public section

namespace GI.CartesianCover

variable {I D : Type*} {H : Subgroup (Equiv.Perm (I → D))}

/-- Coordinate evaluation determines the component homomorphism laws. -/
def ofPermutations (positions : H →* Equiv.Perm I)
    (component : ∀ i : I, coordinateStabilizer positions i → Equiv.Perm D)
    (equivariant : ∀ (i : I) (h : coordinateStabilizer positions i) (x : I → D),
      component i h (x i) = ((h.val : Equiv.Perm (I → D)) x) i) : CartesianCover H where
  positions := positions
  component i :=
    { toFun := component i
      map_one' := by
        apply Equiv.ext
        intro d
        exact equivariant i 1 (fun _ => d)
      map_mul' h k := by
        apply Equiv.ext
        intro d
        calc
          component i (h * k) d =
              (((h * k).val : Equiv.Perm (I → D)) (fun _ => d)) i :=
            equivariant i (h * k) (fun _ => d)
          _ = ((h.val : Equiv.Perm (I → D))
              ((k.val : Equiv.Perm (I → D)) (fun _ => d))) i := rfl
          _ = component i h (((k.val : Equiv.Perm (I → D)) (fun _ => d)) i) :=
            (equivariant i h _).symm
          _ = component i h (component i k d) :=
            congrArg (component i h) (equivariant i k (fun _ => d)).symm }
  equivariant := equivariant

/-- Construct the Cartesian action data directly from the usual product-action
coordinate formula. Component homomorphism laws on stabilizers are derived. -/
def ofCoordinateFormula (positions : H →* Equiv.Perm I)
    (component : H → I → Equiv.Perm D)
    (formula : ∀ (h : H) (i : I) (x : I → D),
      component h i (x i) = ((h : Equiv.Perm (I → D)) x) (positions h i)) :
    CartesianCover H :=
  ofPermutations positions (fun i h => component h.val i) (by
    intro i h x
    rw [formula]
    have hh : positions h.val i = i := h.property
    rw [hh])

end GI.CartesianCover
