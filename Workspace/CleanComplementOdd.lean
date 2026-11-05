module

public import Workspace.CleanComplementConjugates

@[expose] public section

/-! Odd-degree clean complement from one actual localized pair and the supplied
surjective alternating top action. No family of compatible lifts is assumed. -/
namespace GI.CleanOddConstruction
variable {J V : Type*} [Fintype J] [DecidableEq J]
variable {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G (Option (J × Bool))}
variable (d : LocalizedBlockPair A) (hcard : 5 ≤ Fintype.card (Option (J × Bool)))

noncomputable def conjugator (j : J) : G :=
  Classical.choose (d.exists_conjugator hcard none (some (j, false)) (some (j, true))
    (by simp) (by simp) (by simp))

theorem conjugator_spec (j : J) :
    (A.top (conjugator d hcard j)).val d.center = none ∧
    (A.top (conjugator d hcard j)).val ((A.top d.h).val d.center) = some (j, false) ∧
    (A.top (conjugator d hcard j)).val ((A.top d.g).val d.center) = some (j, true) :=
  Classical.choose_spec (d.exists_conjugator hcard none (some (j, false)) (some (j, true))
    (by simp) (by simp) (by simp))

noncomputable def chosenCycle (j : J) : Equiv.Perm V :=
  (conjugator d hcard j).val * d.cycle * (conjugator d hcard j).val⁻¹

theorem chosenCycle_clean (j : J) :
    CleanBlockCycle A.label none (some (j, false)) (some (j, true)) (chosenCycle d hcard j) := by
  obtain ⟨h0, h1, h2⟩ := conjugator_spec d hcard j
  simpa only [chosenCycle, h0, h1, h2] using
    d.clean.conjugate (conjugator d hcard j).val (A.top (conjugator d hcard j)).val
      (A.action (conjugator d hcard j))

theorem chosenCycle_mem (j : J) : chosenCycle d hcard j ∈ G :=
  G.mul_mem (G.mul_mem (conjugator d hcard j).property d.cycle_mem)
    (G.inv_mem (conjugator d hcard j).property)

noncomputable def system : CleanPairSystem J V where
  label := A.label
  cycle := chosenCycle d hcard
  base := Classical.choose (A.label_surjective none)
  base_label := Classical.choose_spec (A.label_surjective none)
  action := fun j => (chosenCycle_clean d hcard j).action
  returns := fun j => (chosenCycle_clean d hcard j).returns
  fixes_other := by
    intro j l hjl b x hx
    apply (chosenCycle_clean d hcard j).fixes x
    · simp [hx]
    · simp [hx, Ne.symm hjl]
    · simp [hx, Ne.symm hjl]

theorem generated_le : Subgroup.closure (Set.range (system d hcard).cycle) ≤ G := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact chosenCycle_mem d hcard j

theorem coordinates_label (b : (system d hcard).Center) (i : Option (J × Bool)) :
    A.label ((system d hcard).coordinates (b, i)) = i :=
  (system d hcard).label_assemble (b, i)

theorem pure_mem (p : alternatingGroup (Option (J × Bool))) :
    coordinatePureLift (system d hcard).coordinates p.val ∈ G := by
  apply generated_le d hcard
  rw [(system d hcard).generated_eq_map]
  exact ⟨p.val, p.property, rfl⟩

noncomputable def sectionHom : alternatingGroup (Option (J × Bool)) →* G :=
  CleanBlockAction.cleanSection (system d hcard).coordinates (pure_mem d hcard)

theorem top_section (p : alternatingGroup (Option (J × Bool))) :
    A.top (sectionHom d hcard p) = p :=
  A.top_cleanSection (system d hcard).coordinates (system d hcard).centerBase
    (coordinates_label d hcard) (pure_mem d hcard) p

theorem section_pure (p : alternatingGroup (Option (J × Bool)))
    (b : (system d hcard).Center) (i : Option (J × Bool)) :
    (sectionHom d hcard p).val ((system d hcard).coordinates (b, i)) =
      (system d hcard).coordinates (b, p.val i) :=
  coordinatePureLift_apply (system d hcard).coordinates p.val b i

/-- The actual subgroup inside G is complementary to the supplied action kernel. -/
theorem kernel_complement : A.top.ker.IsComplement' (sectionHom d hcard).range :=
  A.cleanRange_isComplement (system d hcard).coordinates (system d hcard).centerBase
    (coordinates_label d hcard) (pure_mem d hcard)

theorem kernel_intersection : A.top.ker ⊓ (sectionHom d hcard).range = ⊥ :=
  A.kernel_inf_cleanRange (system d hcard).coordinates (system d hcard).centerBase
    (coordinates_label d hcard) (pure_mem d hcard)

theorem kernel_product (g : G) :
    ∃ k ∈ A.top.ker, ∃ r ∈ (sectionHom d hcard).range, k * r = g :=
  A.kernel_mul_cleanRange (system d hcard).coordinates (system d hcard).centerBase
    (coordinates_label d hcard) (pure_mem d hcard) g

theorem ambient_generated : (sectionHom d hcard).range.map G.subtype =
    Subgroup.closure (Set.range (chosenCycle d hcard)) := by
  change (CleanBlockAction.cleanSection (system d hcard).coordinates (pure_mem d hcard)).range.map
    G.subtype = _
  rw [CleanBlockAction.cleanRange_ambient]
  exact (system d hcard).generated_eq_map.symm

noncomputable def rangeEquiv : alternatingGroup (Option (J × Bool)) ≃* (sectionHom d hcard).range :=
  A.cleanRangeEquiv (system d hcard).coordinates (system d hcard).centerBase
    (coordinates_label d hcard) (pure_mem d hcard)

end GI.CleanOddConstruction
