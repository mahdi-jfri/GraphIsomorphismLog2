module

public import Workspace.Impl.AggItemCiSojPC

@[expose] public section

/-!
# The two complete projected answer cosets cover the matrix transporter

Each nonempty physical query supplies one projected coset with the common source
subgroup. Their union is exactly the permitted transporter. Taking representative
differences therefore gives the full matrix automorphism group, as required by
`leftGroup`, without an additional recursive call.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The two model queries, including the twist only when present. -/
noncomputable def itcsTwists (rep : RectRep P₀ S L W R) : List (permitted W R) :=
  1 :: rep.twist.toList

/-- These are exactly the model's queries and their order. -/
theorem itcs_twists_queries (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) :
    rep.queries M N a₀ = (itcsTwists rep).map (rep.query M N a₀) := by
  cases he : rep.twist <;> simp [RectRep.queries, itcsTwists, he]

/-- The full transporter is the union of the complete projected physical answers. -/
theorem itcs_transporter_union (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (p : permitted W R) :
    MatrixTransports M N p ↔ ∃ t ∈ itcsTwists rep,
      p ∈ t • (itcsRepMap rep '' itcsTypedAnswer rep M N t) := by
  constructor
  · intro hp
    rcases (itcs_transporter_answers rep M N p).1 hp with
      ⟨h, hh, he⟩ | ⟨t, ht, h, hh, he⟩
    · exact ⟨1, List.mem_cons_self .., itcsRepMap rep h, ⟨h, hh, rfl⟩, by simpa using he⟩
    · exact ⟨t, List.mem_cons_of_mem _ (Option.mem_toList.2 ht),
        itcsRepMap rep h, ⟨h, hh, rfl⟩, he⟩
  · rintro ⟨t, -, _, ⟨h, hh, rfl⟩, he⟩
    have htr := (rep.transports_of_mem hh).2
    have ht := RectRep.transports_twist htr
    have hm : (⟨L.π ⟨h.val, rep.le (rep.transports_of_mem hh).1⟩,
        rep.image h.val (rep.transports_of_mem hh).1⟩ : permitted W R) = itcsRepMap rep h := rfl
    change t * itcsRepMap rep h = p at he
    simpa only [hm, he] using ht

/-- The projected representative list fixed by the actual nonempty answers. -/
noncomputable def itcsCosetReps (rep : RectRep P₀ S L W R)
    (rr : permitted W R → Option rep.H) : List (permitted W R) :=
  (itcsTwists rep).filterMap fun t => (rr t).map fun h => t * itcsRepMap rep h

/-- Complete physical answers give exactly a union of the projected source cosets. -/
theorem itcs_coset_cover (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (rr : permitted W R → Option rep.H)
    (hr : ∀ t ∈ itcsTwists rep, match rr t with
      | none => (rep.state M N t).answer = ∅
      | some g => g.val ∈ (rep.state M N t).answer)
    (p : permitted W R) :
    MatrixTransports M N p ↔ ∃ r ∈ itcsCosetReps rep rr,
      p ∈ r • (((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep) :
        Set (permitted W R)) := by
  rw [itcs_transporter_union]
  constructor
  · rintro ⟨t, ht, hp⟩
    cases he : rr t with
    | none =>
      have hempty := hr t ht
      rw [he] at hempty
      obtain ⟨_, ⟨h, hh, -⟩, -⟩ := hp
      have hf : h.val ∈ (∅ : Set (Perm Ω)) := hempty ▸ hh
      exact False.elim hf
    | some g =>
      have hg := hr t ht
      rw [he] at hg
      refine ⟨t * itcsRepMap rep g, ?_, ?_⟩
      · exact List.mem_filterMap.2 ⟨t, ht, by rw [he]; rfl⟩
      · rw [itcs_twisted_answer_coset rep M N t g hg] at hp
        exact hp
  · rintro ⟨r, hrmem, hp⟩
    obtain ⟨t, ht, htr⟩ := List.mem_filterMap.1 hrmem
    cases he : rr t with
    | none => simp only [he, Option.map_none, reduceCtorEq] at htr
    | some g =>
      simp only [he, Option.map_some, Option.some.injEq] at htr
      subst r
      have hg := hr t ht
      rw [he] at hg
      refine ⟨t, ht, ?_⟩
      rwa [itcs_twisted_answer_coset rep M N t g hg]

/-- Differences from a first projected representative, together with the common
source generators, generate the exact matrix automorphism subgroup. -/
theorem itcs_coset_generators (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (rr : permitted W R → Option rep.H)
    (hr : ∀ t ∈ itcsTwists rep, match rr t with
      | none => (rep.state M N t).answer = ∅
      | some g => g.val ∈ (rep.state M N t).answer)
    (gs : List (permitted W R))
    (hg : itcsClosure gs = ((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep))
    {p₀ : permitted W R} (h₀ : p₀ ∈ itcsCosetReps rep rr) :
    itcsClosure (itcsDiffGens p₀ (itcsCosetReps rep rr) gs) = itcsMatrixAut M := by
  apply itcs_matrix_aut_gens M N _ gs h₀
  intro p
  rw [hg]
  exact itcs_coset_cover rep M N rr hr p

end GI.Impl
