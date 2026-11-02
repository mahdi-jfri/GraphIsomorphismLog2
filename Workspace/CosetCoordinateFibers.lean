import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Pi.Lemmas

namespace GI.PrimitiveCartesian

variable {G V I : Type*} {S : I → Type*} [Group G] [MulAction G V]
  [∀ i, Group (S i)]

variable (a : V) (F : (∀ i, S i) →* G) (Q : ∀ i, Subgroup (S i))
  (c : V ≃ (∀ i, S i ⧸ Q i))
  (representatives : ∀ v : V, ∃ x : ∀ i, S i, F x • a = v)
  (coordinates : ∀ (x : ∀ i, S i) i, c (F x • a) i = QuotientGroup.mk (x i))

include representatives coordinates

theorem physical_product_coordinate_action (x : ∀ i, S i) (v : V) (i : I) :
    c (F x • v) i = x i • c v i := by
  obtain ⟨y, rfl⟩ := representatives v
  rw [← mul_smul, ← F.map_mul, coordinates, coordinates]
  rfl

/-- Equality of one actual coset coordinate is exactly the orbit relation
of the complementary product factors. -/
theorem physical_product_coordinate_fiber (i : I) (v w : V) :
    c v i = c w i ↔ ∃ z : ∀ i, S i, z i = 1 ∧ F z • v = w := by
  classical
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := representatives v
    obtain ⟨y, rfl⟩ := representatives w
    rw [coordinates, coordinates] at h
    let z : ∀ j, S j := fun j => if j = i then 1 else y j * (x j)⁻¹
    refine ⟨z, by simp [z], ?_⟩
    apply c.injective
    funext j
    rw [← mul_smul, ← F.map_mul, coordinates, coordinates]
    by_cases hj : j = i
    · subst j
      simpa [z] using h
    · simp only [z, if_neg hj, Pi.mul_apply, inv_mul_cancel_right]
  · rintro ⟨z, hz, rfl⟩
    rw [physical_product_coordinate_action a F Q c representatives coordinates, hz, one_smul]

/-- Conjugation permuting the complementary product factors forces the
ambient physical action to permute coordinate fibers. -/
theorem physical_product_fiber_transport
    (alpha : G → MulAut (∀ i, S i)) (positions : G → Equiv.Perm I)
    (transport : ∀ g x, F (alpha g x) = g * F x * g⁻¹)
    (fibers : ∀ g i x y, x i = y i →
      alpha g x (positions g i) = alpha g y (positions g i))
    (g : G) (i : I) (v w : V) (hvw : c v i = c w i) :
    c (g • v) (positions g i) = c (g • w) (positions g i) := by
  obtain ⟨z, hzi, hzw⟩ :=
    (physical_product_coordinate_fiber a F Q c representatives coordinates i v w).mp hvw
  have hz : alpha g z (positions g i) = 1 := by
    have h := fibers g i z 1 hzi
    simpa only [map_one, Pi.one_apply] using h
  have hact : g • (F z • v) = F (alpha g z) • (g • v) := by
    rw [transport]
    simp only [mul_smul, inv_smul_smul]
  rw [← hzw, hact,
    physical_product_coordinate_action a F Q c representatives coordinates, hz, one_smul]

end GI.PrimitiveCartesian

#print axioms GI.PrimitiveCartesian.physical_product_coordinate_action
#print axioms GI.PrimitiveCartesian.physical_product_coordinate_fiber
#print axioms GI.PrimitiveCartesian.physical_product_fiber_transport
