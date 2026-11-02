import Workspace.StabilizerQuotient
import Mathlib.Algebra.Group.Subgroup.Ker

namespace GI.StabilizerQuotient.Data

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]
variable {φ : G →* Q} {a : V} {b : W}

theorem kernel_orbitRel_iff (d : Data φ a b)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q)
    (x y : V) : MulAction.orbitRel φ.ker V x y ↔ d.map x = d.map y := by
  change (∃ k : φ.ker, (k : G) • y = x) ↔ _
  constructor
  · rintro ⟨k, hk⟩
    exact ((d.fibers_iff_kernel_orbit exactStabilizer y x).mpr ⟨k, k.property, hk⟩).symm
  · intro h
    obtain ⟨k, hk, hxy⟩ := (d.fibers_iff_kernel_orbit exactStabilizer y x).mp h.symm
    exact ⟨⟨k, hk⟩, hxy⟩

/-- The action carrier is the actual set of kernel orbits. -/
noncomputable def kernelOrbitEquiv (d : Data φ a b) (onto : Function.Surjective φ)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q) :
    Quotient (MulAction.orbitRel φ.ker V) ≃ W := by
  let f : Quotient (MulAction.orbitRel φ.ker V) → W :=
    Quotient.lift d.map (fun x y hxy => (d.kernel_orbitRel_iff exactStabilizer x y).mp hxy)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((d.kernel_orbitRel_iff exactStabilizer x y).mpr h)
  · intro w
    obtain ⟨x, rfl⟩ := d.surjective onto targetOrbit w
    exact ⟨Quotient.mk _ x, rfl⟩

theorem kernelOrbitEquiv_apply (d : Data φ a b) (onto : Function.Surjective φ)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q) (x : V) :
    d.kernelOrbitEquiv onto targetOrbit exactStabilizer (Quotient.mk _ x) = d.map x := rfl

theorem kernelOrbitEquiv_equivariant (d : Data φ a b) (onto : Function.Surjective φ)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q)
    (g : G) (x : V) :
    d.kernelOrbitEquiv onto targetOrbit exactStabilizer (Quotient.mk _ (g • x)) =
      φ g • d.kernelOrbitEquiv onto targetOrbit exactStabilizer (Quotient.mk _ x) :=
  d.equivariant g x

/-- Pulling back a permitted subgroup loses no orbit connections. In particular,
the preimage of a transitive rectangle is a single physical subgroup orbit. -/
theorem preimage_orbit_iff (d : Data φ a b) (onto : Function.Surjective φ)
    (exactStabilizer : ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q)
    (P : Subgroup Q) (x y : V) :
    (∃ g : G, φ g ∈ P ∧ g • x = y) ↔ ∃ p : P, (p : Q) • d.map x = d.map y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨φ g, hg⟩, (d.equivariant g x).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨g, hg⟩ := onto p.val
    have heq : d.map (g • x) = d.map y := by rw [d.equivariant, hg, hp]
    obtain ⟨k, hk, hky⟩ := (d.fibers_iff_kernel_orbit exactStabilizer _ _).mp heq
    refine ⟨k * g, ?_, ?_⟩
    · simpa only [map_mul, hk, one_mul, hg] using p.property
    · simpa only [mul_smul] using hky

end GI.StabilizerQuotient.Data
