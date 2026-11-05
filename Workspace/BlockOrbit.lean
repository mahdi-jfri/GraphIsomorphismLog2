module

public import Workspace.BlockBudget

@[expose] public section

namespace GI

variable {H S X B : Type*} [Group H] [Group S]
variable [MulAction H X] [MulAction H B]

/-- Kernel transitivity stated at the active point implies transitivity throughout
its physical orbit. -/
theorem kernel_transitive_on_orbit (φ : H →* S) (a : X)
    (transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • a = h • a) :
    ∀ x y : MulAction.orbit H a, ∃ n : H, φ n = 1 ∧ n • x = y := by
  intro x y
  obtain ⟨g, hg⟩ := x.property
  obtain ⟨h, hh⟩ := y.property
  obtain ⟨n₁, hn₁, h₁⟩ := transitive g
  obtain ⟨n₂, hn₂, h₂⟩ := transitive h
  have hx : n₁ • a = x.val := h₁.trans hg
  have hy : n₂ • a = y.val := h₂.trans hh
  refine ⟨n₂ * n₁⁻¹, by simp [hn₁, hn₂], ?_⟩
  apply Subtype.ext
  change (n₂ * n₁⁻¹) • x.val = y.val
  rw [mul_smul, ← hx, inv_smul_smul, hy]

/-- Actual block localization on the current active orbit. This form remains
valid after arbitrary subgroup restrictions, even when the ambient action is
intransitive. -/
theorem visible_block_orbit_dichotomy [Fintype X] [IsSimpleGroup S]
    (φ : H →* S) (onto : Function.Surjective φ)
    (nonabelian : ∃ s t : S, s * t ≠ t * s)
    (f : X → B)
    (equivariant : ∀ h : H, ∀ x : X, f (h • x) = h • f x)
    (a : X)
    (visible : ∀ h : H,
      (∀ g : H, h • (g • a) = g • a) → φ h = 1)
    (kernel_transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • a = h • a) :
    (∀ h : H, (∀ g : H, h • (g • f a) = g • f a) → φ h = 1) ∨
    ((∀ s : S, ∃ h : H, h • f a = f a ∧ φ h = s) ∧
      (∀ t : H, t • f a = f a →
        (∀ g : H, g • f a = f a → t • (g • a) = g • a) → φ t = 1)) := by
  classical
  let OX := MulAction.orbit H a
  let OB := MulAction.orbit H (f a)
  let a' : OX := ⟨a, MulAction.mem_orbit_self a⟩
  let f' : OX → OB := fun x => ⟨f x.val, by
    obtain ⟨h, hh⟩ := x.property
    exact ⟨h, (equivariant h a).symm.trans (congrArg f hh)⟩⟩
  have hf : Function.Surjective f' := by
    intro b
    obtain ⟨h, hh⟩ := b.property
    refine ⟨⟨h • a, ⟨h, rfl⟩⟩, ?_⟩
    exact Subtype.ext ((equivariant h a).trans hh)
  have heq : ∀ h : H, ∀ x : OX, f' (h • x) = h • f' x := by
    intro h x
    exact Subtype.ext (equivariant h x.val)
  have hv : ∀ h : H, (∀ x : OX, h • x = x) → φ h = 1 := by
    intro h hh
    apply visible h
    intro g
    exact congrArg Subtype.val (hh ⟨g • a, ⟨g, rfl⟩⟩)
  have ht := kernel_transitive_on_orbit φ a kernel_transitive
  have hd := visible_block_dichotomy φ onto nonabelian f' hf heq hv ht a'
  rcases hd with ⟨hblock, _⟩ | ⟨hsurj, hlocal, _⟩
  · left
    intro h hh
    apply hblock h
    intro b
    obtain ⟨g, hg⟩ := b.property
    apply Subtype.ext
    change h • b.val = b.val
    rw [← hg]
    exact hh g
  · right
    constructor
    · intro s
      obtain ⟨h, hh, hs⟩ := hsurj s
      exact ⟨h, congrArg Subtype.val hh, hs⟩
    · intro t ht htfix
      apply hlocal t (Subtype.ext ht)
      intro x hx
      obtain ⟨g, hg⟩ := x.property
      change g • a = x.val at hg
      have hfg : g • f a = f a := by
        have hfx : f x.val = f a := congrArg Subtype.val hx
        rw [← equivariant, hg, hfx]
      apply Subtype.ext
      change t • x.val = x.val
      rw [← hg]
      exact htfix g hfg

end GI
