import Workspace.BlockOrbit

namespace GI

variable {H S X : Type*} [Group H] [Group S] [MulAction H X]

/-- Normal-subgroup orbit localization on an arbitrary current active orbit. -/
theorem every_active_orbit_kernel_killed [Fintype X] [IsSimpleGroup S]
    (U : Subgroup H) [U.Normal] (φ : H →* S)
    (onto : Function.Surjective (φ.comp U.subtype))
    (nonabelian : ∃ s t : S, s * t ≠ t * s) (a : X)
    (transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • a = h • a)
    (visible : ∀ h : H, (∀ g : H, h • (g • a) = g • a) → φ h = 1)
    (k : U) (hk : k ∈ orbitKernel U a) : φ k = 1 := by
  classical
  let a' : MulAction.orbit H a := ⟨a, MulAction.mem_orbit_self a⟩
  have ht : ∀ x y : MulAction.orbit H a, ∃ h : H, h • x = y := by
    intro x y
    obtain ⟨n, _, hn⟩ := kernel_transitive_on_orbit φ a transitive x y
    exact ⟨n, hn⟩
  have hv : ∀ k : U,
      (∀ d : MulAction.orbit H a, (k : H) • d = d) → φ k = 1 := by
    intro k hfix
    apply visible k
    intro g
    exact congrArg Subtype.val (hfix ⟨g • a, ⟨g, rfl⟩⟩)
  apply every_orbit_kernel_killed U φ onto nonabelian ht hv a' k
  intro u
  exact Subtype.ext (hk u)

end GI
