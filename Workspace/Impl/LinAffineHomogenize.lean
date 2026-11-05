module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-! Homogenization of the recentered affine action in Theorem A.20.
The translation is retained, so successive vector layers do not discard it. -/
namespace GI.Impl

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Add a scalar coordinate to turn an affine transformation into a linear one. -/
def linHomogenize (L : V ≃ₗ[R] V) (v : V) : (V × R) ≃ₗ[R] (V × R) where
  toFun x := (L x.1 + x.2 • v, x.2)
  invFun x := (L.symm (x.1 - x.2 • v), x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    ext <;> simp [add_smul] <;> abel
  map_smul' a x := by
    ext <;> simp [smul_add, smul_smul, mul_comm]

@[simp] theorem linHomogenize_apply (L : V ≃ₗ[R] V) (v : V) (x : V × R) :
    linHomogenize L v x = (L x.1 + x.2 • v, x.2) := rfl

@[simp] theorem linHomogenize_one :
    linHomogenize (1 : V ≃ₗ[R] V) (0 : V) = 1 := by
  ext x <;> simp [linHomogenize]

/-- Composition includes the full translation cocycle. -/
theorem linHomogenize_mul (L K : V ≃ₗ[R] V) (v w : V) :
    linHomogenize L v * linHomogenize K w = linHomogenize (L * K) (L w + v) := by
  ext x <;> simp [linHomogenize, smul_add, add_assoc]

/-- A representation and a translation cocycle give an actual linear representation. -/
def linHomogenizedRep {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[R] V))
    (c : G → V) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) :
    G →* ((V × R) ≃ₗ[R] (V × R)) where
  toFun g := linHomogenize (ρ g) (c g)
  map_one' := by
    have hh := hc 1 1
    simp only [one_mul, map_one] at hh
    change c 1 = c 1 + c 1 at hh
    have hz : c 1 = 0 := add_left_cancel (show c 1 + c 1 = c 1 + 0 by simpa using hh.symm)
    rw [map_one, hz]
    exact linHomogenize_one
  map_mul' g h := by rw [linHomogenize_mul, map_mul, hc]

/-- Move the origin to v. The formula uses the left-action convention of
mathlib representations (replace a right-acting g by its inverse). -/
def linRecenterOffset {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[R] V))
    (c : G → V) (v : V) (g : G) : V := ρ g v + c g - v

/-- Recentering preserves the cocycle identity, including the translation term. -/
theorem linRecenterOffset_cocycle {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[R] V))
    (c : G → V) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (v : V) (g h : G) :
    linRecenterOffset ρ c v (g * h) =
      ρ g (linRecenterOffset ρ c v h) + linRecenterOffset ρ c v g := by
  simp only [linRecenterOffset, hc, map_mul, LinearEquiv.mul_apply, map_sub, map_add]
  abel

/-- In centered coordinates the action agrees with the original affine action. -/
theorem linRecenterOffset_action {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[R] V))
    (c : G → V) (v z : V) (g : G) :
    ρ g z + linRecenterOffset ρ c v g = ρ g (z + v) + c g - v := by
  simp only [linRecenterOffset, map_add]
  abel

/-- Stabilizing the homogenized vector is exactly the original affine equation. -/
theorem linHomogenize_fixed (L : V ≃ₗ[R] V) (v x : V) :
    linHomogenize L v (x, 1) = (x, 1) ↔ L x + v = x := by
  simp

/-- Transporting between homogenized vectors is exactly affine transport. -/
theorem linHomogenize_transport (L : V ≃ₗ[R] V) (v x y : V) :
    linHomogenize L v (x, 1) = (y, 1) ↔ L x + v = y := by
  simp

end GI.Impl
