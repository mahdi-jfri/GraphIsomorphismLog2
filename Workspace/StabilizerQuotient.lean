module

public import Workspace.EqualFibers
public import Mathlib.Algebra.Group.Action.Hom

@[expose] public section

namespace GI.StabilizerQuotient

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]

/-- Data from the stabilizer test at one physical vertex. The quotient map
is constructed below; it is not part of the input. -/
structure Data (φ : G →* Q) (a : V) (b : W) where
  sourceOrbit : ∀ x : V, ∃ g : G, g • a = x
  stabilizer : ∀ g : G, g • a = a → φ g • b = b

variable {φ : G →* Q} {a : V} {b : W}

namespace Data

theorem independent (d : Data φ a b) (g h : G) (heq : g • a = h • a) :
    φ g • b = φ h • b := by
  have hfix : (h⁻¹ * g) • a = a := by
    rw [mul_smul, heq, inv_smul_smul]
  have himage := d.stabilizer (h⁻¹ * g) hfix
  rw [map_mul, map_inv, mul_smul] at himage
  have h := congrArg (fun w : W => φ h • w) himage
  simpa only [smul_inv_smul] using h

noncomputable def map (d : Data φ a b) (x : V) : W :=
  φ (Classical.choose (d.sourceOrbit x)) • b

theorem map_smul_base (d : Data φ a b) (g : G) : d.map (g • a) = φ g • b :=
  d.independent _ g (Classical.choose_spec (d.sourceOrbit (g • a)))

theorem map_base (d : Data φ a b) : d.map a = b := by
  have h := d.map_smul_base 1
  simpa using h

theorem equivariant (d : Data φ a b) (g : G) (x : V) :
    d.map (g • x) = φ g • d.map x := by
  obtain ⟨h, rfl⟩ := d.sourceOrbit x
  rw [← mul_smul, d.map_smul_base, map_mul, mul_smul, d.map_smul_base]

theorem surjective (d : Data φ a b) (onto : Function.Surjective φ)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y) : Function.Surjective d.map := by
  intro y
  obtain ⟨q, rfl⟩ := targetOrbit y
  obtain ⟨g, rfl⟩ := onto q
  exact ⟨g • a, d.map_smul_base g⟩

/-- Exact equality of the image of the base stabilizer gives exact kernel
fibers, not merely containment of kernel orbits in the fibers. -/
theorem fibers_iff_kernel_orbit (d : Data φ a b)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q)
    (x y : V) : d.map x = d.map y ↔ ∃ k : G, φ k = 1 ∧ k • x = y := by
  constructor
  · obtain ⟨g, rfl⟩ := d.sourceOrbit x
    obtain ⟨h, rfl⟩ := d.sourceOrbit y
    intro heq
    rw [d.map_smul_base, d.map_smul_base] at heq
    have hfix : φ (h⁻¹ * g) • b = b := by
      rw [map_mul, map_inv, mul_smul, heq, inv_smul_smul]
    obtain ⟨s, hs, hφs⟩ := exactStabilizer _ hfix
    refine ⟨h * s * g⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hφs, map_mul, map_inv]
      simp [mul_assoc]
    · simp only [mul_smul, inv_smul_smul, hs]
  · rintro ⟨k, hk, rfl⟩
    rw [d.equivariant, hk, one_smul]

/-- Equal physical fibers are obtained by actual group transport. -/
theorem fiber_card_eq (d : Data φ a b) (onto : Function.Surjective φ)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y) (u v : W) :
    Nat.card {x // d.map x = u} = Nat.card {x // d.map x = v} := by
  letI : MulAction G W := MulAction.compHom W φ
  apply GI.equivariant_fiber_card_eq d.map d.equivariant _ u v
  intro w z
  obtain ⟨p, rfl⟩ := targetOrbit w
  obtain ⟨q, rfl⟩ := targetOrbit z
  obtain ⟨g, hg⟩ := onto (q * p⁻¹)
  refine ⟨g, ?_⟩
  change φ g • (p • b) = q • b
  rw [hg, mul_smul, inv_smul_smul]

end Data

end GI.StabilizerQuotient
