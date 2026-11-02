import Workspace.Impl.ScriptRun

/-!
# Choices of an aggregation round from a record of the program's choices

Some fields of an aggregation round are functions of mathematical objects: the coset
representatives of `CheckNewWindow` (`Aggregation.reps`, a function of two subgroups) and the
kept representative of a comparison coset (`Aggregation.pick`, a function of a set). A program
computes their values one at a time, as the script asks for them. This file shows that the values
it computes are the values of one such field, provided the program is consistent: it keeps a
record of its choices and gives an argument it has seen before the same value.

* `exists_extend`: a record that is a function on its keys, with every value allowed for its
  key, extends to a choice for every key.
* `CosetRepFn.ofRecord`, `PickFn.ofRecord`: the field built from a consistent record of
  representatives, with the record's values (`ofRecord_reps`, `ofRecord_pick`).
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

/-- A record of choices is **consistent** if equal keys have equal values. -/
def RecordOK {K V : Type} (rec : List (K × V)) : Prop :=
  ∀ p ∈ rec, ∀ p' ∈ rec, p.1 = p'.1 → p.2 = p'.2

theorem RecordOK.nil {K V : Type} : RecordOK ([] : List (K × V)) := by
  intro p hp; simp at hp

/-- Adding a choice for a new key keeps a record consistent. -/
theorem RecordOK.cons_new {K V : Type} {rec : List (K × V)} (h : RecordOK rec) {k : K} {v : V}
    (hk : ∀ p ∈ rec, p.1 ≠ k) : RecordOK ((k, v) :: rec) := by
  intro p hp p' hp' he
  simp only [List.mem_cons] at hp hp'
  rcases hp with rfl | hp <;> rcases hp' with rfl | hp'
  · rfl
  · exact absurd he.symm (hk _ hp')
  · exact absurd he (hk _ hp)
  · exact h p hp p' hp' he

/-- Repeating the recorded choice of a key keeps a record consistent. -/
theorem RecordOK.cons_old {K V : Type} {rec : List (K × V)} (h : RecordOK rec) {k : K} {v : V}
    (hk : (k, v) ∈ rec) : RecordOK ((k, v) :: rec) := by
  intro p hp p' hp' he
  simp only [List.mem_cons] at hp hp'
  rcases hp with rfl | hp <;> rcases hp' with rfl | hp'
  · rfl
  · exact h _ hk p' hp' he
  · exact h p hp _ hk he
  · exact h p hp p' hp' he

/-- **A consistent record extends to a choice for every key**: if every recorded value is allowed
for its key and every key has some allowed value, there is a choice of an allowed value for
every key that agrees with the record. -/
theorem exists_extend {K V : Type} (Q : K → V → Prop) (d : ∀ k, {v // Q k v})
    (rec : List (K × V)) (hok : RecordOK rec) (hQ : ∀ p ∈ rec, Q p.1 p.2) :
    ∃ R : ∀ k, {v // Q k v}, ∀ p ∈ rec, (R p.1).1 = p.2 := by
  classical
  refine ⟨fun k => if h : ∃ p ∈ rec, p.1 = k then
      ⟨h.choose.2, by have := hQ _ h.choose_spec.1; rwa [h.choose_spec.2] at this⟩
    else d k, fun p hp => ?_⟩
  have h : ∃ p' ∈ rec, p'.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [dif_pos h]
  exact hok _ h.choose_spec.1 _ hp h.choose_spec.2

/-! ### Coset representatives -/

/-- What `CosetRepFn` asks of the representatives of one pair of subgroups. -/
def RepsOK {V : Type} (AN : Subgroup (Perm V) × Subgroup (Perm V)) (l : List (Perm V)) : Prop :=
  (∀ τ ∈ l, τ ∈ AN.1) ∧
    (AN.1 : Set (Perm V)) ⊆ ⋃ τ ∈ l, τ • (AN.2 : Set (Perm V)) ∧
    l.length ≤ Nat.card (AN.1 ⧸ AN.2.subgroupOf AN.1)

/-- **The coset representatives of a consistent record**: the recorded representatives for the
recorded pairs of subgroups, and those of `R₀` for the others. -/
noncomputable def CosetRepFn.ofRecord {V : Type} (R₀ : CosetRepFn V)
    (rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V)))
    (hok : RecordOK rec) (hQ : ∀ p ∈ rec, RepsOK p.1 p.2) : CosetRepFn V :=
  let R := (exists_extend RepsOK (fun AN => ⟨R₀.reps AN.1 AN.2,
    fun _ h => R₀.mem h, R₀.cover _ _, R₀.length_le _ _⟩) rec hok hQ).choose
  { reps := fun A N => (R (A, N)).1
    mem := fun h => (R _).2.1 _ h
    cover := fun A N => (R (A, N)).2.2.1
    length_le := fun A N => (R (A, N)).2.2.2 }

/-- The coset representatives of a consistent record are the recorded ones. -/
theorem CosetRepFn.ofRecord_reps {V : Type} (R₀ : CosetRepFn V)
    (rec : List ((Subgroup (Perm V) × Subgroup (Perm V)) × List (Perm V)))
    (hok : RecordOK rec) (hQ : ∀ p ∈ rec, RepsOK p.1 p.2) {A N : Subgroup (Perm V)}
    {l : List (Perm V)} (h : ((A, N), l) ∈ rec) :
    (CosetRepFn.ofRecord R₀ rec hok hQ).reps A N = l :=
  (exists_extend RepsOK (fun AN => ⟨R₀.reps AN.1 AN.2,
    fun _ h => R₀.mem h, R₀.cover _ _, R₀.length_le _ _⟩) rec hok hQ).choose_spec _ h

/-! ### Representatives of comparison cosets -/

/-- What `PickFn` asks of the representative of one set. -/
def PickOK {V : Type} (A : Set (Perm V)) (o : Option (Perm V)) : Prop :=
  (∀ g, o = some g → g ∈ A) ∧ (o = none ↔ A = ∅)

/-- **The representatives of a consistent record** of comparison cosets. -/
noncomputable def PickFn.ofRecord {V : Type} (rec : List (Set (Perm V) × Option (Perm V)))
    (hok : RecordOK rec) (hQ : ∀ p ∈ rec, PickOK p.1 p.2) : PickFn V :=
  let R := (exists_extend PickOK (fun A => ⟨pickRep A, fun _ h => pickRep_mem h,
    pickRep_eq_none⟩) rec hok hQ).choose
  { pick := fun A => (R A).1
    mem := fun h => (R _).2.1 _ h
    eq_none := (R _).2.2 }

/-- The representatives of a consistent record are the recorded ones. -/
theorem PickFn.ofRecord_pick {V : Type} (rec : List (Set (Perm V) × Option (Perm V)))
    (hok : RecordOK rec) (hQ : ∀ p ∈ rec, PickOK p.1 p.2) {A : Set (Perm V)}
    {o : Option (Perm V)} (h : (A, o) ∈ rec) : (PickFn.ofRecord rec hok hQ).pick A = o :=
  (exists_extend PickOK (fun A => ⟨pickRep A, fun _ h => pickRep_mem h, pickRep_eq_none⟩) rec
    hok hQ).choose_spec _ h

end GI.Impl
