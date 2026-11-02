import Workspace.PrimitiveSubsetCoordinates

namespace GI.AlternatingActions

open scoped Pointwise

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Singletons identify the one-subset action with the natural action. -/
noncomputable def singletonSubsetEquiv : A ≃ Johnson.SubsetVertex A 1 :=
  Equiv.ofBijective (fun x => ⟨{x}, Finset.card_singleton x⟩)
    ⟨fun _ _ he => Finset.singleton_injective (congrArg Subtype.val he), fun s => by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.property
      exact ⟨x, Subtype.ext hx.symm⟩⟩

omit [Fintype A] in
theorem subsetAction_singleton (p : Equiv.Perm A) (x : A) :
    Johnson.subsetAction 1 p (singletonSubsetEquiv x) = singletonSubsetEquiv (p x) := by
  apply Subtype.ext
  change p • ({x} : Finset A) = {p x}
  simp

omit [Fintype A] in
theorem singletonSubsetEquiv_symm_equivariant (p : Equiv.Perm A)
    (s : Johnson.SubsetVertex A 1) :
    singletonSubsetEquiv.symm (Johnson.subsetAction 1 p s) =
      p (singletonSubsetEquiv.symm s) := by
  obtain ⟨x, rfl⟩ := singletonSubsetEquiv.surjective s
  rw [subsetAction_singleton, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable {V : Type*} (G : Subgroup (Equiv.Perm A)) [MulAction G V]

omit [Fintype A] in
/-- Equivariant subset coordinates identify the entire physical image
with the actual subset action image of the given natural group. -/
theorem subset_coordinates_image {t : ℕ} (e : V ≃ Johnson.SubsetVertex A t)
    (equivariant : ∀ (g : G) (v : V),
      e (g • v) = Johnson.subsetAction t (g : Equiv.Perm A) (e v)) :
    (MulAction.toPermHom G V).range.map (GI.relabelPerm e).toMonoidHom =
      G.map (Johnson.subsetAction t) := by
  have conjugates (g : G) :
      GI.relabelPerm e (MulAction.toPermHom G V g) =
        Johnson.subsetAction t (g : Equiv.Perm A) := by
    apply Equiv.ext
    intro s
    change e (g • e.symm s) = _
    rw [equivariant, e.apply_symm_apply]
  ext p
  constructor
  · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
    exact ⟨g.val, g.property, (conjugates g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨MulAction.toPermHom G V ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, conjugates ⟨g, hg⟩⟩

omit [Fintype A] in
theorem subset_coordinates_image_le {t : ℕ} (e : V ≃ Johnson.SubsetVertex A t)
    (equivariant : ∀ (g : G) (v : V),
      e (g • v) = Johnson.subsetAction t (g : Equiv.Perm A) (e v)) :
    (MulAction.toPermHom G V).range.map (GI.relabelPerm e).toMonoidHom ≤
      Johnson.subsetImage t := by
  rw [subset_coordinates_image G e equivariant]
  rintro p ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

omit [MulAction G V] [DecidableEq A] in
theorem subset_coordinates_degree {t : ℕ} (e : V ≃ Johnson.SubsetVertex A t) :
    Nat.card V = Nat.choose (Fintype.card A) t := by
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Johnson.card_subsetVertex]

variable [Nontrivial V] [MulAction.IsPreprimitive G V]

/-- The actual intransitive-stabilizer branch is the natural action or
a Johnson action of size at least two and at most half the natural degree.
This assumes only the explicit natural alternating inclusion, and does
not assert an automorphism classification of alternating groups. -/
theorem natural_or_johnson_of_intransitive_stabilizer
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Fintype.card A) (a : V)
    (intransitive : ¬ MulAction.IsPretransitive
      ((MulAction.stabilizer G a).map G.subtype) A) :
    (∃ e : V ≃ A, ∀ (g : G) (v : V), e (g • v) = (g : Equiv.Perm A) (e v)) ∨
    ∃ t : ℕ, 2 ≤ t ∧ 2 * t ≤ Fintype.card A ∧
      ∃ e : V ≃ Johnson.SubsetVertex A t,
        (∀ (g : G) (v : V),
          e (g • v) = Johnson.subsetAction t (g : Equiv.Perm A) (e v)) ∧
        (MulAction.toPermHom G V).range.map (GI.relabelPerm e).toMonoidHom ≤
          Johnson.subsetImage t := by
  obtain ⟨t, ht, hhalf, e, he⟩ := coordinates_of_intransitive_stabilizer
    G giant hdegree a intransitive
  by_cases hone : t = 1
  · subst t
    left
    refine ⟨e.trans singletonSubsetEquiv.symm, ?_⟩
    intro g v
    change singletonSubsetEquiv.symm (e (g • v)) = _
    rw [he, singletonSubsetEquiv_symm_equivariant]
    rfl
  · exact Or.inr ⟨t, by omega, hhalf, e, he, subset_coordinates_image_le G e he⟩

end GI.AlternatingActions
