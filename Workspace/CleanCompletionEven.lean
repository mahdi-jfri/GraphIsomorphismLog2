import Workspace.CleanCompletionCoordinates
import Mathlib.GroupTheory.Perm.Option

/-! Compatible extension of already fixed clean coordinates by one new block. -/
namespace GI.CleanEvenCoordinates
variable {I B W : Type*} [DecidableEq I]

/-- Old blocks already have coordinates B × I; the new block is identified by t. -/
def coordinates (t : B ≃ W) : B × Option I ≃ (B × I) ⊕ W where
  toFun p := match p.2 with
    | none => Sum.inr (t p.1)
    | some i => Sum.inl (p.1, i)
  invFun x := match x with
    | Sum.inl p => (p.1, some p.2)
    | Sum.inr w => (t.symm w, none)
  left_inv := by
    rintro ⟨b, i⟩
    cases i <;> simp
  right_inv := by
    intro x
    cases x <;> simp

def oldHom : Equiv.Perm I →* Equiv.Perm ((B × I) ⊕ W) where
  toFun p := Equiv.sumCongr (cleanPureHom p) (Equiv.refl W)
  map_one' := by apply Equiv.ext; intro x; cases x <;> rfl
  map_mul' _ _ := by apply Equiv.ext; intro x; cases x <;> rfl

def lift (t : B ≃ W) : Equiv.Perm (Option I) →* Equiv.Perm ((B × I) ⊕ W) :=
  (relabelPerm (coordinates t)).toMonoidHom.comp cleanPureHom

omit [DecidableEq I] in
theorem lift_option (t : B ≃ W) (p : Equiv.Perm I) :
    lift t p.optionCongr = oldHom p := by
  apply Equiv.ext
  intro x
  cases x with
  | inl x => rfl
  | inr w =>
    change Sum.inr (t (t.symm w)) = Sum.inr w
    rw [t.apply_symm_apply]

/-- The extra clean cycle has the paper's fixed old correspondence b → a.
Its new correspondence a → W is the actual block bijection t. -/
structure CompatibleCycle (t : B ≃ W) (a b : I)
    (c : Equiv.Perm ((B × I) ⊕ W)) : Prop where
  to_new : ∀ x : B, c (Sum.inl (x, a)) = Sum.inr (t x)
  back : ∀ x : B, c (Sum.inl (x, b)) = Sum.inl (x, a)
  returns : ∀ x, c (c (c x)) = x
  fixes_other : ∀ (x : B) (i : I), i ≠ a → i ≠ b → c (Sum.inl (x, i)) = Sum.inl (x, i)

theorem lift_cycle (t : B ≃ W) (a b : I) (hab : a ≠ b)
    (c : Equiv.Perm ((B × I) ⊕ W)) (hc : CompatibleCycle t a b c) :
    lift t (cleanCycle (some a) none (some b)) = c := by
  have hmiddle : ∀ x : B, c (Sum.inr (t x)) = Sum.inl (x, b) := by
    intro x
    have h := hc.returns (Sum.inl (x, b))
    rwa [hc.back, hc.to_new] at h
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := (coordinates t).surjective x
  change (coordinates t) (cleanPureHom (cleanCycle (some a) none (some b))
    ((coordinates t).symm ((coordinates t) p))) = _
  rw [(coordinates t).symm_apply_apply]
  obtain ⟨x, i⟩ := p
  cases i with
  | none =>
    simpa [coordinates, cleanPureHom, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      using (hmiddle x).symm
  | some i =>
    by_cases hia : i = a
    · subst i
      simpa [coordinates, cleanPureHom, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab]
        using (hc.to_new x).symm
    by_cases hib : i = b
    · subst i
      simpa [coordinates, cleanPureHom, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        hab, Ne.symm hab] using (hc.back x).symm
    · simpa [coordinates, cleanPureHom, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hia, hib]
        using (hc.fixes_other x i hia hib).symm

variable [Fintype I]

def generated (c : Equiv.Perm ((B × I) ⊕ W)) : Subgroup (Equiv.Perm ((B × I) ⊕ W)) :=
  Subgroup.closure (oldHom '' (alternatingGroup I : Set (Equiv.Perm I)) ∪ {c})

/-- The old clean alternating group and one compatible extra cycle generate
exactly the pure alternating group in the extended coordinates. -/
theorem generated_eq_map (t : B ≃ W) (a b : I) (hab : a ≠ b)
    (c : Equiv.Perm ((B × I) ⊕ W)) (hc : CompatibleCycle t a b c) :
    generated c = (alternatingGroup (Option I)).map (lift t) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro p (⟨q, hq, rfl⟩ | hp)
    · refine ⟨q.optionCongr, ?_, lift_option t q⟩
      change Equiv.Perm.sign q = 1 at hq
      change Equiv.Perm.sign q.optionCongr = 1
      rw [Equiv.optionCongr_sign]
      exact hq
    · have hpc : p = c := hp
      refine ⟨cleanCycle (some a) none (some b), ?_, (lift_cycle t a b hab c hc).trans hpc.symm⟩
      exact Equiv.Perm.IsThreeCycle.mem_alternatingGroup
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simpa using hab) (by simp) (by simp))
  · have hAlt : alternatingGroup (Option I) ≤ (generated c).comap (lift t) := by
      apply alternating_le_one_point_extension _ (some a) (some b) none
        (by simpa using hab) (by simp) (by simp)
      · intro p hp hfix
        let q := Equiv.removeNone p
        have hqeq : q.optionCongr = p := by
          dsimp [q]
          rw [map_equiv_removeNone, hfix]
          simp
        have hq : q ∈ alternatingGroup I := by
          rw [Equiv.Perm.mem_alternatingGroup] at hp ⊢
          have he := Equiv.optionCongr_sign q
          rw [hqeq] at he
          exact he.symm.trans hp
        change lift t p ∈ generated c
        rw [← hqeq, lift_option]
        exact Subgroup.subset_closure (Or.inl ⟨q, hq, rfl⟩)
      · change lift t (cleanCycle (some a) (some b) none) ∈ generated c
        have hcmem : c ∈ generated c := Subgroup.subset_closure (Or.inr rfl)
        have heq : lift t (cleanCycle (some a) (some b) none) = c⁻¹ := by
          rw [← cleanCycle_inv (some a) none (some b), map_inv, lift_cycle t a b hab c hc]
        rw [heq]
        exact (generated c).inv_mem hcmem
    rintro p ⟨q, hq, rfl⟩
    exact hAlt hq

noncomputable def generatedEquiv (t : B ≃ W) (base : B) (a b : I) (hab : a ≠ b)
    (c : Equiv.Perm ((B × I) ⊕ W)) (hc : CompatibleCycle t a b c) :
    alternatingGroup (Option I) ≃* generated c := by
  let f := (lift t).comp (alternatingGroup (Option I)).subtype
  have hf : Function.Injective f :=
    ((relabelPerm (coordinates t)).injective.comp (cleanPureHom_injective base)).comp Subtype.val_injective
  have hr : f.range = generated c := by
    rw [generated_eq_map t a b hab c hc]
    simp only [f, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)

end GI.CleanEvenCoordinates
