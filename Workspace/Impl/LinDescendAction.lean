module

public import Workspace.Impl.LinDescendAdd
public import Workspace.Impl.AddEquivGroup

@[expose] public section

/-! The descended maps form an action, and the projected translations retain
the cocycle law. -/
namespace GI.Impl

variable {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]

noncomputable def linDescendAction (π : V →+ W) (hπ : Function.Surjective π)
    (ρ : G →* (V ≃+ V)) (hk : ∀ g x, π x = 0 → π (ρ g x) = 0) (g : G) : W ≃+ W :=
  linDescendEquiv π hπ (ρ g) (hk g) (by
    intro x hx
    simpa only [map_inv, addEquiv_inv_apply] using hk g⁻¹ x hx)

@[simp] theorem linDescendAction_image (π : V →+ W) (hπ : Function.Surjective π)
    (ρ : G →* (V ≃+ V)) (hk : ∀ g x, π x = 0 → π (ρ g x) = 0) (g : G) (x : V) :
    linDescendAction π hπ ρ hk g (π x) = π (ρ g x) := by
  unfold linDescendAction
  exact linDescendEquiv_image _ _ _ _ _ x

noncomputable def linDescendRep (π : V →+ W) (hπ : Function.Surjective π)
    (ρ : G →* (V ≃+ V)) (hk : ∀ g x, π x = 0 → π (ρ g x) = 0) : G →* (W ≃+ W) where
  toFun := linDescendAction π hπ ρ hk
  map_one' := by
    apply AddEquiv.ext
    intro w
    obtain ⟨x, rfl⟩ := hπ w
    simp only [linDescendAction_image, map_one]
    rfl
  map_mul' g h := by
    apply AddEquiv.ext
    intro w
    obtain ⟨x, rfl⟩ := hπ w
    change linDescendAction π hπ ρ hk (g * h) (π x) =
      linDescendAction π hπ ρ hk g (linDescendAction π hπ ρ hk h (π x))
    simp only [linDescendAction_image, map_mul]
    rfl

@[simp] theorem linDescendRep_image (π : V →+ W) (hπ : Function.Surjective π)
    (ρ : G →* (V ≃+ V)) (hk : ∀ g x, π x = 0 → π (ρ g x) = 0) (g : G) (x : V) :
    linDescendRep π hπ ρ hk g (π x) = π (ρ g x) := linDescendAction_image π hπ ρ hk g x

theorem linDescendRep_cocycle (π : V →+ W) (hπ : Function.Surjective π)
    (ρ : G →* (V ≃+ V)) (hk : ∀ g x, π x = 0 → π (ρ g x) = 0) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) :
    π (c (g * h)) = linDescendRep π hπ ρ hk g (π (c h)) + π (c g) := by
  rw [hc, map_add, linDescendRep_image]

end GI.Impl
