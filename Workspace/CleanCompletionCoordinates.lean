import Workspace.Compat
import Workspace.CleanCompletion
import Workspace.LocalCommutator
import Workspace.OrbitBudget

/-! Coordinates constructed from actual clean cycles sharing one central block. -/
namespace GI

/-- A.16 supplies the individual clean return-map identity required below. -/
theorem local_commutator_return {V : Type*} (g h : Equiv.Perm V)
    (sep : LocalSeparated g h) (x : V) :
    rightLocalCommutator g h (rightLocalCommutator g h (rightLocalCommutator g h x)) = x := by
  by_cases hx : ∃ a, localIntersection g h a ∧ x ∈ localTriple g h a
  · obtain ⟨a, ha, hx⟩ := hx
    simp only [localTriple, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [local_commutator_first g h sep ha, local_commutator_second g h sep ha,
        local_commutator_third g h sep ha]
    · rw [local_commutator_second g h sep ha, local_commutator_third g h sep ha,
        local_commutator_first g h sep ha]
    · rw [local_commutator_third g h sep ha, local_commutator_first g h sep ha,
        local_commutator_second g h sep ha]
  · have h0 : ¬localIntersection g h x := fun ha => hx ⟨x, ha, by simp [localTriple]⟩
    have hg : ¬localIntersection g h (g.symm x) :=
      fun ha => hx ⟨g.symm x, ha, by simp [localTriple]⟩
    have hh : ¬localIntersection g h (h.symm x) :=
      fun ha => hx ⟨h.symm x, ha, by simp [localTriple]⟩
    have hf := local_commutator_outside g h h0 hg hh
    rw [hf, hf, hf]

variable {J V : Type*} [DecidableEq J]

/-- Concrete clean block cycles. The hypotheses concern only their individual
three-block action, return map, and pointwise support; no cross-cycle relation is assumed. -/
structure CleanPairSystem (J V : Type*) [DecidableEq J] where
  label : V → Option (J × Bool)
  cycle : J → Equiv.Perm V
  base : V
  base_label : label base = none
  action : ∀ j x, label (cycle j x) = pairedCleanCycle j (label x)
  returns : ∀ j x, cycle j (cycle j (cycle j x)) = x
  fixes_other : ∀ j l : J, j ≠ l → ∀ (b : Bool) (x : V),
    label x = some (l, b) → cycle j x = x

namespace CleanPairSystem

abbrev Center (s : CleanPairSystem J V) := {x : V // s.label x = none}

def centerBase (s : CleanPairSystem J V) : s.Center := ⟨s.base, s.base_label⟩

/-- Transport the central block around each of its two private blocks. -/
def assemble (s : CleanPairSystem J V) (p : s.Center × Option (J × Bool)) : V :=
  match p.2 with
  | none => p.1.val
  | some (j, false) => s.cycle j p.1.val
  | some (j, true) => s.cycle j (s.cycle j p.1.val)

theorem label_assemble (s : CleanPairSystem J V) (p : s.Center × Option (J × Bool)) :
    s.label (s.assemble p) = p.2 := by
  obtain ⟨x, i⟩ := p
  cases i with
  | none => exact x.property
  | some p =>
    obtain ⟨j, b⟩ := p
    cases b <;> simp [assemble, s.action, x.property, pairedCleanCycle, cleanCycle,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem label_inverse (s : CleanPairSystem J V) (j : J) (x : V) :
    s.label ((s.cycle j)⁻¹ x) = (pairedCleanCycle j)⁻¹ (s.label x) := by
  apply (pairedCleanCycle j).injective
  rw [← s.action, Equiv.Perm.apply_inv_self, Equiv.Perm.apply_inv_self]

theorem assemble_injective (s : CleanPairSystem J V) : Function.Injective s.assemble := by
  rintro ⟨x, i⟩ ⟨y, j⟩ he
  have hi : i = j := by simpa only [s.label_assemble] using congrArg s.label he
  subst j
  have hxy : x = y := by
    apply Subtype.ext
    cases i with
    | none => exact he
    | some p =>
      obtain ⟨j, b⟩ := p
      cases b
      · exact (s.cycle j).injective he
      · exact (s.cycle j).injective ((s.cycle j).injective he)
  exact congrArg (fun x => (x, i)) hxy

theorem assemble_surjective (s : CleanPairSystem J V) : Function.Surjective s.assemble := by
  intro x
  cases he : s.label x with
  | none => exact ⟨(⟨x, he⟩, none), rfl⟩
  | some p =>
    obtain ⟨j, b⟩ := p
    cases b
    · have hy : s.label ((s.cycle j)⁻¹ x) = none := by
        rw [s.label_inverse, he]
        simp [pairedCleanCycle, cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      exact ⟨(⟨(s.cycle j)⁻¹ x, hy⟩, some (j, false)), (s.cycle j).apply_symm_apply x⟩
    · have hy : s.label ((s.cycle j)⁻¹ ((s.cycle j)⁻¹ x)) = none := by
        rw [s.label_inverse, s.label_inverse, he]
        simp [pairedCleanCycle, cleanCycle, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      refine ⟨(⟨(s.cycle j)⁻¹ ((s.cycle j)⁻¹ x), hy⟩, some (j, true)), ?_⟩
      simp [assemble]

/-- The one coordinate identification simultaneously makes all chosen cycles pure. -/
noncomputable def coordinates (s : CleanPairSystem J V) :
    s.Center × Option (J × Bool) ≃ V :=
  Equiv.ofBijective s.assemble ⟨s.assemble_injective, s.assemble_surjective⟩

theorem cycle_assemble (s : CleanPairSystem J V) (j : J)
    (p : s.Center × Option (J × Bool)) :
    s.cycle j (s.assemble p) = s.assemble (p.1, pairedCleanCycle j p.2) := by
  obtain ⟨x, i⟩ := p
  cases i with
  | none =>
    simp [assemble, pairedCleanCycle, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  | some p =>
    obtain ⟨l, b⟩ := p
    by_cases hjl : j = l
    · subst l
      cases b
      · simp [assemble, pairedCleanCycle, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      · simpa [assemble, pairedCleanCycle, cleanCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
          using s.returns j x.val
    · have hfix := s.fixes_other j l hjl b (s.assemble (x, some (l, b)))
        (s.label_assemble (x, some (l, b)))
      have hindex : pairedCleanCycle j (some (l, b)) = some (l, b) := by
        cases b <;> simp [pairedCleanCycle, cleanCycle, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def, Ne.symm hjl]
      rw [hindex]
      exact hfix

end CleanPairSystem

def cleanPureHom {B I : Type*} : Equiv.Perm I →* Equiv.Perm (B × I) where
  toFun p := Equiv.prodCongr (Equiv.refl B) p
  map_one' := by apply Equiv.ext; intro x; rfl
  map_mul' _ _ := by apply Equiv.ext; intro x; rfl

theorem cleanPureHom_injective {B I : Type*} (b : B) :
    Function.Injective (cleanPureHom (B := B) (I := I)) := by
  intro p q hpq
  apply Equiv.ext
  intro i
  exact congrArg Prod.snd (congrArg (fun f : Equiv.Perm (B × I) => f (b, i)) hpq)

namespace CleanPairSystem

noncomputable def lift (s : CleanPairSystem J V) : Equiv.Perm (Option (J × Bool)) →* Equiv.Perm V :=
  (relabelPerm s.coordinates).toMonoidHom.comp cleanPureHom

theorem lift_injective (s : CleanPairSystem J V) : Function.Injective s.lift :=
  (relabelPerm s.coordinates).injective.comp (cleanPureHom_injective s.centerBase)

theorem lift_generator (s : CleanPairSystem J V) (j : J) :
    s.lift (pairedCleanCycle j) = s.cycle j := by
  apply Equiv.ext
  intro x
  obtain ⟨p, rfl⟩ := s.coordinates.surjective x
  change s.coordinates (cleanPureHom (pairedCleanCycle j) (s.coordinates.symm (s.coordinates p))) = _
  rw [s.coordinates.symm_apply_apply]
  exact (s.cycle_assemble j p).symm

theorem generated_eq_map [Fintype J] (s : CleanPairSystem J V) :
    Subgroup.closure (Set.range s.cycle) = (alternatingGroup (Option (J × Bool))).map s.lift := by
  have heq : s.lift '' Set.range (pairedCleanCycle (J := J)) = Set.range s.cycle := by
    ext p
    constructor
    · rintro ⟨q, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (s.lift_generator j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨pairedCleanCycle j, ⟨j, rfl⟩, s.lift_generator j⟩
  rw [← paired_clean_cycles_generate, MonoidHom.map_closure, heq]

/-- The subgroup generated by the supplied compatible lifts really is Alt,
with all relations derived from the constructed coordinates. -/
noncomputable def generatedEquiv [Fintype J] (s : CleanPairSystem J V) :
    alternatingGroup (Option (J × Bool)) ≃* Subgroup.closure (Set.range s.cycle) := by
  let f := s.lift.comp (alternatingGroup (Option (J × Bool))).subtype
  have hf : Function.Injective f := s.lift_injective.comp Subtype.val_injective
  have hr : f.range = Subgroup.closure (Set.range s.cycle) := by
    rw [s.generated_eq_map]
    simp only [f, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)

end CleanPairSystem
end GI
