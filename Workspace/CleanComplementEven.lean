import Workspace.CleanComplementConjugates

/-! Build the compatible extra cycle from a pure old cycle and one localized
lift. All CleanExtension fields, including the old return map, are proved. -/
namespace GI.CleanEvenConstruction
open CleanEvenCoordinates
variable {I B W : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm ((B × I) ⊕ W))}
variable (A : CleanBlockAction G (Option I))
variable (hlabel : ∀ x, A.label x = blockLabel x)

include hlabel in
theorem old_localized (p : Equiv.Perm I) :
    LocalizedBlockLift A.label p.optionCongr (oldHom p) where
  action := by
    intro x
    rw [hlabel, hlabel]
    cases x <;> rfl
  fixes := by
    intro x hx
    rw [hlabel] at hx
    cases x with
    | inl x =>
      have hi : p x.2 = x.2 := Option.some.inj hx
      change Sum.inl (x.1, p x.2) = Sum.inl x
      rw [hi]
    | inr w => rfl

structure ExtraLift (a b c : I) where
  h : G
  localized : LocalizedBlockLift A.label (A.top h).val h.val
  sends : (A.top h).val (some a) = none
  fixes_b : (A.top h).val (some b) = some b
  fixes_c : (A.top h).val (some c) = some c

variable {A} {a b c : I} (d : ExtraLift A a b c)
variable (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)

include hab hbc in
omit [Fintype I] in
theorem old_cycle_first : cleanCycle a b c a = b := by
  simp [cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Ne.symm hab, hbc]

include hab hac hbc in
theorem old_cycle_even : cleanCycle a b c ∈ alternatingGroup I :=
  Equiv.Perm.IsThreeCycle.mem_alternatingGroup
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab (Ne.symm hbc))

include hab hbc in
theorem top_meet : ∀ i : Option I,
    ((cleanCycle a b c).optionCongr i ≠ i ∧ (A.top d.h).val i ≠ i) ↔ i = some a := by
  intro i
  cases i with
  | none => simp
  | some i =>
    change ((some (cleanCycle a b c i) : Option I) ≠ some i ∧
      (A.top d.h).val (some i) ≠ some i) ↔ some i = some a
    by_cases hia : i = a
    · subst i
      rw [old_cycle_first hab hbc, d.sends]
      simp [Ne.symm hab]
    by_cases hib : i = b
    · subst i
      rw [d.fixes_b]
      simp [hia]
    by_cases hic : i = c
    · subst i
      rw [d.fixes_c]
      simp [hia]
    · have hp : cleanCycle a b c i = i := by
        simp [cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hia, hib, hic]
      simp [hp, hia]

def extraCycle : Equiv.Perm ((B × I) ⊕ W) :=
  rightLocalCommutator (oldHom (cleanCycle a b c)) d.h.val

include hlabel hab hbc in
theorem extra_clean : CleanBlockCycle A.label (some a) none (some b) (extraCycle d) := by
  have hc := cleanBlockCycle_of_localized (old_localized A hlabel (cleanCycle a b c))
    d.localized (some a) (top_meet d hab hbc)
  have hg : (cleanCycle a b c).optionCongr (some a) = some b :=
    congrArg some (old_cycle_first hab hbc)
  simpa only [d.sends, hg] using hc

include hlabel hab hbc in
theorem extra_extension : CleanExtension a b (extraCycle d) where
  action := by
    intro x
    have ht := (extra_clean hlabel d hab hbc).action x
    simpa only [hlabel] using ht
  back := by
    intro x
    have hl := old_localized A hlabel (cleanCycle a b c)
    have hs := localized_separated hl d.localized (some a) (top_meet d hab hbc)
    have hx : localIntersection (oldHom (cleanCycle a b c)) d.h.val (Sum.inl (x, a)) :=
      (localized_intersection hl d.localized (some a) (top_meet d hab hbc) _).mpr
        (hlabel (Sum.inl (x, a)))
    have ht := local_commutator_third (oldHom (cleanCycle a b c)) d.h.val hs hx
    have hg : oldHom (W := W) (cleanCycle a b c) (Sum.inl (x, a)) = Sum.inl (x, b) :=
      congrArg (fun i => (Sum.inl (x, i) : (B × I) ⊕ W)) (old_cycle_first hab hbc)
    rwa [hg] at ht
  returns := (extra_clean hlabel d hab hbc).returns
  fixes_other := by
    intro x i hia hib
    apply (extra_clean hlabel d hab hbc).fixes
    · simpa only [hlabel, blockLabel, ne_eq, Option.some.injEq] using hia
    · simp only [hlabel, blockLabel, ne_eq, reduceCtorEq, not_false_eq_true]
    · simpa only [hlabel, blockLabel, ne_eq, Option.some.injEq] using hib

variable (old_mem : ∀ p : alternatingGroup I, oldHom p.val ∈ G)

include hab hac hbc old_mem in
theorem extra_mem : (extraCycle d) ∈ G :=
  local_commutator_mem G (old_mem ⟨cleanCycle a b c, old_cycle_even hab hac hbc⟩) d.h.property

include hab hac hbc old_mem in
theorem generated_le : generated (extraCycle d) ≤ G := by
  apply (Subgroup.closure_le _).mpr
  rintro p (⟨q, hq, rfl⟩ | hp)
  · exact old_mem ⟨q, hq⟩
  · have he : p = (extraCycle d) := hp
    rw [he]
    exact extra_mem d hab hac hbc old_mem

noncomputable def coords : B × Option I ≃ (B × I) ⊕ W :=
  coordinates (extra_extension hlabel d hab hbc).transfer

theorem coordinates_label (x : B) (i : Option I) :
    A.label (coords hlabel d hab hbc (x, i)) = i := by
  rw [hlabel]
  cases i <;> rfl

include hac old_mem in
theorem pure_mem (p : alternatingGroup (Option I)) :
    coordinatePureLift (coords hlabel d hab hbc) p.val ∈ G := by
  apply generated_le d hab hac hbc old_mem
  rw [(extra_extension hlabel d hab hbc).generated_eq_map hab]
  exact ⟨p.val, p.property, rfl⟩

noncomputable def sectionHom : alternatingGroup (Option I) →* G :=
  CleanBlockAction.cleanSection (coords hlabel d hab hbc)
    (pure_mem hlabel d hab hac hbc old_mem)

theorem top_section (base : B) (p : alternatingGroup (Option I)) :
    A.top (sectionHom hlabel d hab hac hbc old_mem p) = p :=
  A.top_cleanSection (coords hlabel d hab hbc) base
    (coordinates_label hlabel d hab hbc) (pure_mem hlabel d hab hac hbc old_mem) p

theorem section_pure (p : alternatingGroup (Option I)) (x : B) (i : Option I) :
    (sectionHom hlabel d hab hac hbc old_mem p).val (coords hlabel d hab hbc (x, i)) =
      coords hlabel d hab hbc (x, p.val i) :=
  coordinatePureLift_apply (coords hlabel d hab hbc) p.val x i

theorem kernel_complement (base : B) :
    A.top.ker.IsComplement' (sectionHom hlabel d hab hac hbc old_mem).range :=
  A.cleanRange_isComplement (coords hlabel d hab hbc) base
    (coordinates_label hlabel d hab hbc) (pure_mem hlabel d hab hac hbc old_mem)

theorem kernel_intersection (base : B) :
    A.top.ker ⊓ (sectionHom hlabel d hab hac hbc old_mem).range = ⊥ :=
  A.kernel_inf_cleanRange (coords hlabel d hab hbc) base
    (coordinates_label hlabel d hab hbc) (pure_mem hlabel d hab hac hbc old_mem)

theorem kernel_product (base : B) (g : G) :
    ∃ k ∈ A.top.ker, ∃ r ∈ (sectionHom hlabel d hab hac hbc old_mem).range, k * r = g :=
  A.kernel_mul_cleanRange (coords hlabel d hab hbc) base
    (coordinates_label hlabel d hab hbc) (pure_mem hlabel d hab hac hbc old_mem) g

end GI.CleanEvenConstruction
