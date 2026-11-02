import Workspace.StabilizerOrbit

namespace GI.StabilizerQuotient

variable {G Q V W : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q W]

/-- Construct the quotient data from equality of actual point-stabilizer images. -/
def ofStabilizerImage (φ : G →* Q) (a : V) (b : W)
    (sourceOrbit : ∀ x : V, ∃ g : G, g • a = x)
    (image : (MulAction.stabilizer G a).map φ = MulAction.stabilizer Q b) : Data φ a b where
  sourceOrbit := sourceOrbit
  stabilizer g hg := by
    have hm : φ g ∈ (MulAction.stabilizer G a).map φ := ⟨g, hg, rfl⟩
    rw [image] at hm
    exact hm

theorem exact_stabilizer_of_image (φ : G →* Q) (a : V) (b : W)
    (image : (MulAction.stabilizer G a).map φ = MulAction.stabilizer Q b) :
    ∀ q : Q, q • b = b → ∃ s : G, s • a = a ∧ φ s = q := by
  intro q hq
  have hm : q ∈ (MulAction.stabilizer G a).map φ := by rw [image]; exact hq
  exact hm

/-- Output of a physical quotient construction. These fields are proved when
the value is constructed; they are not structural assumptions on the input. -/
structure KernelQuotient (φ : G →* Q) (V W : Type*) [MulAction G V] [MulAction Q W] where
  map : V → W
  onto : Function.Surjective map
  equivariant : ∀ (g : G) (x : V), map (g • x) = φ g • map x
  kernel_fibers : ∀ x y : V, map x = map y ↔ ∃ k : G, φ k = 1 ∧ k • x = y
  equal_fibers : ∀ u v : W, Nat.card {x // map x = u} = Nat.card {x // map x = v}

noncomputable def kernelQuotientOfImage (φ : G →* Q) (a : V) (b : W)
    (onto : Function.Surjective φ)
    (sourceOrbit : ∀ x : V, ∃ g : G, g • a = x)
    (targetOrbit : ∀ y : W, ∃ q : Q, q • b = y)
    (image : (MulAction.stabilizer G a).map φ = MulAction.stabilizer Q b) :
    KernelQuotient φ V W where
  map := (ofStabilizerImage φ a b sourceOrbit image).map
  onto := (ofStabilizerImage φ a b sourceOrbit image).surjective onto targetOrbit
  equivariant := (ofStabilizerImage φ a b sourceOrbit image).equivariant
  kernel_fibers := (ofStabilizerImage φ a b sourceOrbit image).fibers_iff_kernel_orbit
    (exact_stabilizer_of_image φ a b image)
  equal_fibers := (ofStabilizerImage φ a b sourceOrbit image).fiber_card_eq onto targetOrbit

end GI.StabilizerQuotient
