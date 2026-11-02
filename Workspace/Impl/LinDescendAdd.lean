import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Tactic

/-! Descend additive actions through a surjective coordinate projection whose
kernel they preserve. This supplies primary actions without enumerating a
quotient or assuming that its action is faithful. -/
namespace GI.Impl

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

theorem linDescendCongr (π : V →+ W) (f : V →+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) {x y : V} (hxy : π x = π y) : π (f x) = π (f y) := by
  have hxy0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have he := hf (x - y) hxy0
  simp only [map_sub] at he
  exact sub_eq_zero.mp he

noncomputable def linDescendMap (π : V →+ W) (hπ : Function.Surjective π) (f : V →+ V) (w : W) : W :=
  π (f (hπ w).choose)

theorem linDescendMap_image (π : V →+ W) (hπ : Function.Surjective π) (f : V →+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (x : V) : linDescendMap π hπ f (π x) = π (f x) :=
  linDescendCongr π f hf (hπ (π x)).choose_spec

noncomputable def linDescendHom (π : V →+ W) (hπ : Function.Surjective π) (f : V →+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) : W →+ W where
  toFun := linDescendMap π hπ f
  map_zero' := by simpa only [map_zero] using linDescendMap_image π hπ f hf 0
  map_add' u v := by
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨y, rfl⟩ := hπ v
    rw [← π.map_add, linDescendMap_image π hπ f hf, linDescendMap_image π hπ f hf,
      linDescendMap_image π hπ f hf, f.map_add, π.map_add]

@[simp] theorem linDescendHom_image (π : V →+ W) (hπ : Function.Surjective π) (f : V →+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (x : V) : linDescendHom π hπ f hf (π x) = π (f x) :=
  linDescendMap_image π hπ f hf x

theorem linDescendHom_comp (π : V →+ W) (hπ : Function.Surjective π) (f g : V →+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (hg : ∀ x, π x = 0 → π (g x) = 0) :
    (linDescendHom π hπ f hf).comp (linDescendHom π hπ g hg) =
      linDescendHom π hπ (f.comp g) (fun x hx => hf (g x) (hg x hx)) := by
  apply AddMonoidHom.ext
  intro w
  obtain ⟨x, rfl⟩ := hπ w
  simp only [AddMonoidHom.comp_apply, linDescendHom_image]

noncomputable def linDescendEquiv (π : V →+ W) (hπ : Function.Surjective π) (f : V ≃+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (hi : ∀ x, π x = 0 → π (f.symm x) = 0) : W ≃+ W where
  toFun := linDescendMap π hπ f.toAddMonoidHom
  invFun := linDescendMap π hπ f.symm.toAddMonoidHom
  left_inv w := by
    obtain ⟨x, rfl⟩ := hπ w
    rw [linDescendMap_image π hπ f.toAddMonoidHom hf,
      linDescendMap_image π hπ f.symm.toAddMonoidHom hi]
    exact congrArg π (f.symm_apply_apply x)
  right_inv w := by
    obtain ⟨x, rfl⟩ := hπ w
    rw [linDescendMap_image π hπ f.symm.toAddMonoidHom hi,
      linDescendMap_image π hπ f.toAddMonoidHom hf]
    exact congrArg π (f.apply_symm_apply x)
  map_add' := (linDescendHom π hπ f.toAddMonoidHom hf).map_add

@[simp] theorem linDescendEquiv_image (π : V →+ W) (hπ : Function.Surjective π) (f : V ≃+ V)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (hi : ∀ x, π x = 0 → π (f.symm x) = 0) (x : V) :
    linDescendEquiv π hπ f hf hi (π x) = π (f x) := linDescendMap_image π hπ f.toAddMonoidHom hf x

end GI.Impl
