import Workspace.CleanCompletionEven

/-! Construct the even completion's transfer bijection from the actual clean cycle. -/
namespace GI.CleanEvenCoordinates
variable {I B W : Type*} [DecidableEq I]

def blockLabel : (B × I) ⊕ W → Option I
  | Sum.inl p => some p.2
  | Sum.inr _ => none

/-- Individual block-action data of the compatible extra cycle. -/
structure CleanExtension (a b : I) (c : Equiv.Perm ((B × I) ⊕ W)) : Prop where
  action : ∀ x, blockLabel (c x) = cleanCycle (some a) none (some b) (blockLabel x)
  back : ∀ x : B, c (Sum.inl (x, b)) = Sum.inl (x, a)
  returns : ∀ x, c (c (c x)) = x
  fixes_other : ∀ (x : B) (i : I), i ≠ a → i ≠ b → c (Sum.inl (x, i)) = Sum.inl (x, i)

theorem cleanExtension_top_a (a b : I) :
    cleanCycle (some a) none (some b) (some a) = none := by
  simp [cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem CleanExtension.goes_to_new {a b : I} {c : Equiv.Perm ((B × I) ⊕ W)}
    (hc : CleanExtension a b c) (x : B) :
    ∃ w : W, c (Sum.inl (x, a)) = Sum.inr w := by
  have ht : blockLabel (c (Sum.inl (x, a))) = none :=
    (hc.action _).trans (cleanExtension_top_a a b)
  cases hx : c (Sum.inl (x, a)) with
  | inl p => simp [hx, blockLabel] at ht
  | inr w => exact ⟨w, rfl⟩

noncomputable def CleanExtension.transferMap {a b : I} {c : Equiv.Perm ((B × I) ⊕ W)}
    (hc : CleanExtension a b c) (x : B) : W :=
  Classical.choose (hc.goes_to_new x)

theorem CleanExtension.transferMap_spec {a b : I} {c : Equiv.Perm ((B × I) ⊕ W)}
    (hc : CleanExtension a b c) (x : B) :
    c (Sum.inl (x, a)) = Sum.inr (hc.transferMap x) :=
  Classical.choose_spec (hc.goes_to_new x)

theorem CleanExtension.transferMap_bijective {a b : I}
    {c : Equiv.Perm ((B × I) ⊕ W)} (hc : CleanExtension a b c) :
    Function.Bijective hc.transferMap := by
  constructor
  · intro x y hxy
    have h := c.injective ((hc.transferMap_spec x).trans
      ((congrArg Sum.inr hxy).trans (hc.transferMap_spec y).symm))
    exact congrArg Prod.fst (Sum.inl.inj h)
  · intro w
    obtain ⟨z, hz⟩ := c.surjective (Sum.inr w)
    have ht := hc.action z
    rw [hz] at ht
    have hi : blockLabel z = some a := by
      apply (cleanCycle (some a) none (some b)).injective
      exact ht.symm.trans (cleanExtension_top_a a b).symm
    cases z with
    | inl p =>
      obtain ⟨x, i⟩ := p
      have hia : i = a := Option.some.inj hi
      subst i
      exact ⟨x, Sum.inr.inj ((hc.transferMap_spec x).symm.trans hz)⟩
    | inr _ => simp [blockLabel] at hi

/-- This is the actual map from the old a-block onto the new block. -/
noncomputable def CleanExtension.transfer {a b : I}
    {c : Equiv.Perm ((B × I) ⊕ W)} (hc : CleanExtension a b c) : B ≃ W :=
  Equiv.ofBijective hc.transferMap hc.transferMap_bijective

theorem CleanExtension.compatible {a b : I} {c : Equiv.Perm ((B × I) ⊕ W)}
    (hc : CleanExtension a b c) : CompatibleCycle hc.transfer a b c where
  to_new := hc.transferMap_spec
  back := hc.back
  returns := hc.returns
  fixes_other := hc.fixes_other

theorem CleanExtension.pure {a b : I} {c : Equiv.Perm ((B × I) ⊕ W)}
    (hc : CleanExtension a b c) (hab : a ≠ b) :
    lift hc.transfer (cleanCycle (some a) none (some b)) = c :=
  lift_cycle _ a b hab c hc.compatible

theorem CleanExtension.generated_eq_map [Fintype I] {a b : I}
    {c : Equiv.Perm ((B × I) ⊕ W)} (hc : CleanExtension a b c) (hab : a ≠ b) :
    generated c = (alternatingGroup (Option I)).map (lift hc.transfer) :=
  GI.CleanEvenCoordinates.generated_eq_map _ a b hab c hc.compatible

noncomputable def CleanExtension.generatedEquiv [Fintype I] {a b : I}
    {c : Equiv.Perm ((B × I) ⊕ W)} (hc : CleanExtension a b c) (hab : a ≠ b) (base : B) :
    alternatingGroup (Option I) ≃* generated c :=
  GI.CleanEvenCoordinates.generatedEquiv _ base a b hab c hc.compatible

end GI.CleanEvenCoordinates
