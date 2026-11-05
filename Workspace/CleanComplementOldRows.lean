module

public import Workspace.CleanComplementConjugates

@[expose] public section

/-! The odd construction on all but one block, with the remaining block fixed.
This supplies the old pure subgroup needed by the even construction. -/
namespace GI.CleanOldRows
open CleanEvenCoordinates
variable {J V : Type*} [Fintype J] [DecidableEq J]
variable {G : Subgroup (Equiv.Perm V)}
variable {A : CleanBlockAction G (Option (Option (J × Bool)))}
variable (d : LocalizedBlockPair A) (hcard : 5 ≤ Fintype.card (Option (Option (J × Bool))))

noncomputable def conjugator (j : J) : G :=
  Classical.choose (d.exists_conjugator hcard (some none) (some (some (j, false)))
    (some (some (j, true))) (by simp) (by simp) (by simp))

theorem conjugator_spec (j : J) :
    (A.top (conjugator d hcard j)).val d.center = some none ∧
    (A.top (conjugator d hcard j)).val ((A.top d.h).val d.center) = some (some (j, false)) ∧
    (A.top (conjugator d hcard j)).val ((A.top d.g).val d.center) = some (some (j, true)) :=
  Classical.choose_spec (d.exists_conjugator hcard (some none) (some (some (j, false)))
    (some (some (j, true))) (by simp) (by simp) (by simp))

noncomputable def chosenCycle (j : J) : Equiv.Perm V :=
  (conjugator d hcard j).val * d.cycle * (conjugator d hcard j).val⁻¹

theorem chosen_clean (j : J) : CleanBlockCycle A.label (some none)
    (some (some (j, false))) (some (some (j, true))) (chosenCycle d hcard j) := by
  obtain ⟨h0, h1, h2⟩ := conjugator_spec d hcard j
  simpa only [chosenCycle, h0, h1, h2] using d.clean.conjugate (conjugator d hcard j).val
    (A.top (conjugator d hcard j)).val (A.action (conjugator d hcard j))

theorem chosen_mem (j : J) : chosenCycle d hcard j ∈ G :=
  G.mul_mem (G.mul_mem (conjugator d hcard j).property d.cycle_mem)
    (G.inv_mem (conjugator d hcard j).property)

abbrev Old := {x : V // A.label x ≠ none}
abbrev New := {x : V // A.label x = none}

theorem old_label_exists (x : Old (A := A)) : ∃ i, A.label x.val = some i := by
  cases hx : A.label x.val with
  | none => exact False.elim (x.property hx)
  | some i => exact ⟨i, rfl⟩

noncomputable def oldLabel (x : Old (A := A)) : Option (J × Bool) :=
  Classical.choose (old_label_exists x)

theorem oldLabel_spec (x : Old (A := A)) : A.label x.val = some (oldLabel x) :=
  Classical.choose_spec (old_label_exists x)

theorem option_cleanCycle {T : Type*} [DecidableEq T] (a b c : T) :
    (cleanCycle a b c).optionCongr = cleanCycle (some a) (some b) (some c) := by
  have hswap : ∀ a b x : T,
      Equiv.swap (some a) (some b) (some x) = some (Equiv.swap a b x) := by
    intro a b x
    by_cases ha : x = a
    · subst x
      simp
    by_cases hb : x = b
    · subst x
      simp
    · simp [Equiv.swap_apply_def, ha, hb]
  apply Equiv.ext
  intro x
  cases x with
  | none => simp [cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  | some x =>
    change some (Equiv.swap a c (Equiv.swap a b x)) =
      Equiv.swap (some a) (some c) (Equiv.swap (some a) (some b) (some x))
    rw [hswap, hswap]

theorem old_preserved (j : J) (x : V) :
    A.label x ≠ none ↔ A.label (chosenCycle d hcard j x) ≠ none := by
  rw [(chosen_clean d hcard j).action, ← option_cleanCycle]
  cases A.label x <;> simp

noncomputable def cycle (j : J) : Equiv.Perm (Old (A := A)) :=
  (chosenCycle d hcard j).subtypePerm (fun x => (old_preserved d hcard j x).symm)

theorem cycle_action (j : J) (x : Old (A := A)) :
    oldLabel (cycle d hcard j x) = pairedCleanCycle j (oldLabel x) := by
  apply Option.some.inj
  rw [← oldLabel_spec]
  change A.label (chosenCycle d hcard j x.val) = _
  rw [(chosen_clean d hcard j).action, oldLabel_spec, ← option_cleanCycle]
  rfl

noncomputable def base : Old (A := A) :=
  ⟨Classical.choose (A.label_surjective (some none)), by
    rw [Classical.choose_spec (A.label_surjective (some none))]
    simp⟩

theorem base_label : oldLabel (base (A := A)) = none := by
  apply Option.some.inj
  exact (oldLabel_spec (base (A := A))).symm.trans
    (Classical.choose_spec (A.label_surjective (some none)))

noncomputable def system : CleanPairSystem J (Old (A := A)) where
  label := oldLabel
  cycle := cycle d hcard
  base := base
  base_label := base_label
  action := cycle_action d hcard
  returns := by
    intro j x
    apply Subtype.ext
    exact (chosen_clean d hcard j).returns x.val
  fixes_other := by
    intro j l hjl b x hx
    apply Subtype.ext
    apply (chosen_clean d hcard j).fixes x.val
    · simp [oldLabel_spec, hx]
    · simp [oldLabel_spec, hx, Ne.symm hjl]
    · simp [oldLabel_spec, hx, Ne.symm hjl]

def merge : Old (A := A) ⊕ New (A := A) → V := Sum.elim Subtype.val Subtype.val

theorem merge_bijective : Function.Bijective (merge (A := A)) := by
  constructor
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y => exact False.elim (x.property ((congrArg A.label hxy).trans y.property))
    | inr x =>
      cases y with
      | inl y => exact False.elim (y.property ((congrArg A.label hxy.symm).trans x.property))
      | inr y => exact congrArg Sum.inr (Subtype.ext hxy)
  · intro x
    by_cases hx : A.label x = none
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩

noncomputable def mergeEquiv : Old (A := A) ⊕ New (A := A) ≃ V :=
  Equiv.ofBijective merge merge_bijective

noncomputable def coordinates :
    ((system d hcard).Center × Option (J × Bool)) ⊕ New (A := A) ≃ V :=
  (Equiv.sumCongr (system d hcard).coordinates (Equiv.refl _)).trans mergeEquiv

theorem coordinates_label
    (x : ((system d hcard).Center × Option (J × Bool)) ⊕ New (A := A)) :
    A.label (coordinates d hcard x) = blockLabel x := by
  cases x with
  | inl p =>
    exact (oldLabel_spec ((system d hcard).assemble p)).trans
      (congrArg some ((system d hcard).label_assemble p))
  | inr x => exact x.property

noncomputable def lift : Equiv.Perm (Option (J × Bool)) →* Equiv.Perm V :=
  (relabelPerm (coordinates d hcard)).toMonoidHom.comp oldHom

theorem lift_generator (j : J) : lift d hcard (pairedCleanCycle j) = chosenCycle d hcard j := by
  apply Equiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (coordinates d hcard).surjective x
  change coordinates d hcard (oldHom (pairedCleanCycle j)
    ((coordinates d hcard).symm (coordinates d hcard z))) = _
  rw [(coordinates d hcard).symm_apply_apply]
  cases z with
  | inl p =>
    exact congrArg Subtype.val ((system d hcard).cycle_assemble j p).symm
  | inr w =>
    exact ((chosen_clean d hcard j).fixes w.val (by simp [w.property])
      (by simp [w.property]) (by simp [w.property])).symm

theorem generated_eq_map : Subgroup.closure (Set.range (chosenCycle d hcard)) =
    (alternatingGroup (Option (J × Bool))).map (lift d hcard) := by
  have he : lift d hcard '' Set.range (pairedCleanCycle (J := J)) = Set.range (chosenCycle d hcard) := by
    ext p
    constructor
    · rintro ⟨q, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (lift_generator d hcard j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨pairedCleanCycle j, ⟨j, rfl⟩, lift_generator d hcard j⟩
  rw [← paired_clean_cycles_generate, MonoidHom.map_closure, he]

theorem pure_mem (p : alternatingGroup (Option (J × Bool))) : lift d hcard p.val ∈ G := by
  have hle : Subgroup.closure (Set.range (chosenCycle d hcard)) ≤ G := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact chosen_mem d hcard j
  apply hle
  rw [generated_eq_map]
  exact ⟨p.val, p.property, rfl⟩

end GI.CleanOldRows
