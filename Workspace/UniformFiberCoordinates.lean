import Workspace.DependentFiberCoordinates
import Mathlib.GroupTheory.GroupAction.Basic

namespace GI.CartesianCoordinates

variable {G V I : Type*} {D : I → Type*} [Group G] [MulAction G V]

def actionInCoordinates (c : V ≃ (∀ i, D i)) (g : G) : Equiv.Perm (∀ i, D i) where
  toFun x := c (g • c.symm x)
  invFun x := c (g⁻¹ • c.symm x)
  left_inv x := by simp
  right_inv x := by simp

/-- Transitivity on coordinate positions and actual fiber preservation
construct equivalences between the coordinate types. -/
noncomputable def coordinateTransport (background : ∀ i, D i)
    (c : V ≃ (∀ i, D i)) (p : G →* Equiv.Perm I)
    (fibers : ∀ g i x y, c x i = c y i → c (g • x) (p g i) = c (g • y) (p g i))
    (transitive : ∀ i j, ∃ g : G, p g i = j) (i j : I) : D i ≃ D j := by
  classical
  let g := Classical.choose (transitive i j)
  have hg : p g i = j := Classical.choose_spec (transitive i j)
  refine GI.CartesianCover.betweenFibers background (actionInCoordinates c g) i j ?_ ?_
  · intro x y hxy
    change c (g • c.symm x) j = c (g • c.symm y) j
    have h := fibers g i (c.symm x) (c.symm y) (by simpa using hxy)
    exact hg ▸ h
  · intro x y hxy
    change c (g⁻¹ • c.symm x) i = c (g⁻¹ • c.symm y) i
    have hji : p (g⁻¹) j = i := by
      rw [← hg, map_inv]
      exact (p g).symm_apply_apply i
    have h := fibers (g⁻¹) j (c.symm x) (c.symm y) (by simpa using hxy)
    exact hji ▸ h

/-- Uniform Cartesian coordinates are constructed from the actual
dependent coordinates, with one chosen coordinate as the common domain. -/
noncomputable def uniformCoordinates (background : ∀ i, D i)
    (c : V ≃ (∀ i, D i)) (p : G →* Equiv.Perm I)
    (fibers : ∀ g i x y, c x i = c y i → c (g • x) (p g i) = c (g • y) (p g i))
    (transitive : ∀ i j, ∃ g : G, p g i = j) (base : I) : V ≃ (I → D base) :=
  c.trans (Equiv.piCongrRight (fun i => coordinateTransport background c p fibers transitive i base))

theorem uniformCoordinates_fibers (background : ∀ i, D i)
    (c : V ≃ (∀ i, D i)) (p : G →* Equiv.Perm I)
    (fibers : ∀ g i x y, c x i = c y i → c (g • x) (p g i) = c (g • y) (p g i))
    (transitive : ∀ i j, ∃ g : G, p g i = j) (base : I)
    (g : G) (i : I) (x y : V)
    (hxy : uniformCoordinates background c p fibers transitive base x i =
      uniformCoordinates background c p fibers transitive base y i) :
    uniformCoordinates background c p fibers transitive base (g • x) (p g i) =
      uniformCoordinates background c p fibers transitive base (g • y) (p g i) := by
  change coordinateTransport background c p fibers transitive (p g i) base
      (c (g • x) (p g i)) =
    coordinateTransport background c p fibers transitive (p g i) base (c (g • y) (p g i))
  apply congrArg (coordinateTransport background c p fibers transitive (p g i) base)
  apply fibers g i x y
  apply (coordinateTransport background c p fibers transitive i base).injective
  exact hxy

end GI.CartesianCoordinates

#print axioms GI.CartesianCoordinates.actionInCoordinates
#print axioms GI.CartesianCoordinates.coordinateTransport
#print axioms GI.CartesianCoordinates.uniformCoordinates
#print axioms GI.CartesianCoordinates.uniformCoordinates_fibers
