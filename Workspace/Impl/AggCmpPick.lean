import Workspace.Impl.AggCmpCall

/-!
# The pick cache of the comparison phase

The lockstep run keeps one representative `Pk.pick A` of each comparison coset `A`. The round
fixes no choice (`Aggregation.pick` is a field), so the program makes the choice the first time
it meets a set and must make the same choice when it meets the same set again: the candidate
rounds are those whose `pick` agrees with the record of the choices made so far (`CmPicks`).

Each set the program meets is empty or a coset `g H`. For the empty set every `PickFn` gives
`none` (`cm_pick_empty`), so nothing is recorded. A nonempty coset is kept as an entry `(H, g)`
of the cache, with the choice `g`. Two cosets are equal exactly when their groups are equal and
`g⁻¹ g' ∈ H` (`cm_coset_eq_iff`): the group test of `AggCache.lean` and one **Membership** test.

* `CmCacheOK ents rec`: the record is the list of the entries with their choices, and the
  entries stand for distinct sets. Then the record is consistent and allowed
  (`CmCacheOK.recordOK`, `CmCacheOK.pickOK`), so it has candidates (`cmPicks_nonempty`).
* `CmCacheOK.hit`: a set equal to that of an entry has the entry's choice, for every candidate.
* `CmCacheOK.miss`: a set that differs from those of all entries may be added with any of its
  elements as the choice.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {V : Type}

/-- **Two cosets are equal** exactly when their groups are equal and `g⁻¹ g'` lies in the group. -/
theorem cm_coset_eq_iff {H H' : Subgroup (Perm V)} {g g' : Perm V} :
    g • (H : Set (Perm V)) = g' • (H' : Set (Perm V)) ↔ H = H' ∧ g⁻¹ * g' ∈ H := by
  constructor
  · intro h
    have hg' : g' ∈ g • (H : Set (Perm V)) := by
      rw [h]; exact ⟨1, H'.one_mem, by simp⟩
    obtain ⟨u, hu, hgu⟩ := hg'
    simp only [smul_eq_mul] at hgu
    have hm : g⁻¹ * g' ∈ H := by rw [← hgu, inv_mul_cancel_left]; exact hu
    refine ⟨?_, hm⟩
    -- `g H = g' H`, so `g' H = g' H'`, so `H = H'`
    have h1 : g' • (H : Set (Perm V)) = g • (H : Set (Perm V)) := by
      ext x
      simp only [Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨g⁻¹ * g' * v, H.mul_mem hm hv, by group⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨(g⁻¹ * g')⁻¹ * v, H.mul_mem (H.inv_mem hm) hv, by group⟩
    rw [← h1] at h
    have h2 := congrArg (fun s : Set (Perm V) => g'⁻¹ • s) h
    simp only [inv_smul_smul] at h2
    exact SetLike.coe_injective h2
  · rintro ⟨rfl, hm⟩
    ext x
    simp only [Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(g⁻¹ * g')⁻¹ * v, H.mul_mem (H.inv_mem hm) hv, by group⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g⁻¹ * g' * v, H.mul_mem hm hv, by group⟩

/-- Every choice of representatives gives `none` for the empty set. -/
theorem cm_pick_empty (Pk : PickFn V) : Pk.pick ∅ = none := Pk.eq_none.2 rfl

/-! ### The cache -/

/-- An entry of the cache: a group `H` and the choice `g`, for the coset `g H`. -/
abbrev CmEnt (V : Type) := Subgroup (Perm V) × Perm V

/-- The set of an entry. -/
def cmEntSet (E : CmEnt V) : Set (Perm V) := E.2 • (E.1 : Set (Perm V))

/-- The record of an entry. -/
def cmEntRec (E : CmEnt V) : Set (Perm V) × Option (Perm V) := (cmEntSet E, some E.2)

/-- **A good cache**: the record lists the entries with their choices, and the entries stand for
distinct sets. -/
def CmCacheOK (ents : List (CmEnt V)) (rec : List (Set (Perm V) × Option (Perm V))) : Prop :=
  rec = ents.map cmEntRec ∧ (ents.map cmEntSet).Nodup

theorem CmCacheOK.nil : CmCacheOK ([] : List (CmEnt V)) [] := ⟨rfl, List.nodup_nil⟩

theorem cm_mem_entSet (E : CmEnt V) : E.2 ∈ cmEntSet E :=
  ⟨1, E.1.one_mem, by simp⟩

/-- The record of a good cache is consistent. -/
theorem CmCacheOK.recordOK {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) : RecordOK rec := by
  obtain ⟨rfl, hnd⟩ := h
  intro p hp p' hp' he
  obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hp
  obtain ⟨E', hE', rfl⟩ := List.mem_map.1 hp'
  rw [List.inj_on_of_nodup_map hnd hE hE' he]

/-- The choices of a good cache are allowed. -/
theorem CmCacheOK.pickOK {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) : ∀ p ∈ rec, PickOK p.1 p.2 := by
  obtain ⟨rfl, -⟩ := h
  intro p hp
  obtain ⟨E, -, rfl⟩ := List.mem_map.1 hp
  refine ⟨fun g hg => ?_, ?_⟩
  · cases hg
    exact cm_mem_entSet E
  · simp only [cmEntRec, reduceCtorEq, false_iff]
    exact Set.nonempty_iff_ne_empty.1 ⟨_, cm_mem_entSet E⟩

/-- A good cache has candidates. -/
theorem CmCacheOK.nonempty {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) : (CmPicks rec).Nonempty :=
  cmPicks_nonempty h.recordOK h.pickOK

/-- **A hit**: a set equal to that of an entry has the entry's choice, for every candidate. -/
theorem CmCacheOK.hit {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) {E : CmEnt V} (hE : E ∈ ents) {A : Set (Perm V)}
    (hA : cmEntSet E = A) {Pk : PickFn V} (hP : Pk ∈ CmPicks rec) : Pk.pick A = some E.2 := by
  refine cmPicks_pick hP (A := A) ?_
  rw [h.1, ← hA]
  exact List.mem_map_of_mem hE

/-- **A miss**: a new set may be added with its choice. -/
theorem CmCacheOK.miss {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) {E : CmEnt V} (hE : ∀ E' ∈ ents, cmEntSet E' ≠ cmEntSet E) :
    CmCacheOK (E :: ents) (cmEntRec E :: rec) := by
  refine ⟨by rw [h.1]; rfl, ?_⟩
  rw [List.map_cons]
  refine List.nodup_cons.2 ⟨fun hm => ?_, h.2⟩
  obtain ⟨E', hE', he⟩ := List.mem_map.1 hm
  exact hE E' hE' he

/-- The candidates of a miss: those of the old record that choose `g` for the new set. -/
theorem cmPicks_miss {rec : List (Set (Perm V) × Option (Perm V))} (E : CmEnt V) {Pk : PickFn V} :
    Pk ∈ CmPicks (cmEntRec E :: rec) ↔ Pk ∈ CmPicks rec ∧ Pk.pick (cmEntSet E) = some E.2 := by
  constructor
  · intro hP
    exact ⟨cmPicks_cons _ hP, hP _ List.mem_cons_self⟩
  · rintro ⟨hP, hp⟩ p hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact hp
    · exact hP p hp'

end GI.Impl
