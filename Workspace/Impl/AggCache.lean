module

public import Workspace.Impl.AggChoice
public import Workspace.Impl.AggClos

@[expose] public section

/-!
# The cache of coset representatives

The coset representatives of a round are a field of the aggregation round,
`Aggregation.reps : CosetRepFn S.dom`, one function of two subgroups `(A, N)` fixed before the
script runs. The program computes representatives as the rounds come, from generator lists. The
same pair `(A, N)` can come twice: the loops of `x` and `y` for one test set start at the same
stage `(P_T, ∅)`, and two test sets can reach the same stage. So the program keeps a cache: for
every pair it has seen, the graph forms of the lifts of `A` and `N` and the representatives it
chose. Before it computes representatives for a pair, it looks the pair up; two pairs are the
same exactly when each generating list lies in the group of the other (cited **Membership**).

* `liftGroup_injOn`, `graphOf_injOn`: a subgroup of `G|_dom` is determined by the graph of its
  lift, so equal graph forms mean equal subgroups (`eq_iff_le_gens`).
* `CacheOK c rec`: the cache `c` (graph forms and representatives on positions) stands for the
  record `rec` of the choices (`AggChoice.lean`), which is consistent and allowed.
* `CacheOK.hit`: a cache entry with the same pair gives the recorded representatives, so
  `CosetRepFn.ofRecord` returns them (`ofRecord_reps`).
* `CacheOK.miss`: a pair not in the cache can be added with any allowed representatives.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)
open scoped Pointwise

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-! ### Subgroups from graph forms -/

/-- **A subgroup of `G|_dom` is determined by its lift.** -/
theorem liftGroup_injOn {A A' : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hA' : A' ≤ S.domGroup) (h : S.liftGroup A = S.liftGroup A') : A = A' := by
  have key : ∀ {B B' : Subgroup (Perm S.dom)}, B ≤ S.domGroup →
      S.liftGroup B = S.liftGroup B' → B ≤ B' := by
    intro B B' hB he p hp
    obtain ⟨g, rfl⟩ := hB hp
    have h1 : (g : Perm Ω) ∈ S.liftGroup B := State.mem_liftGroup.2 ⟨g.2, hp⟩
    rw [he] at h1
    obtain ⟨_, h2⟩ := State.mem_liftGroup.1 h1
    exact h2
  exact le_antisymm (key hA h) (key hA' h.symm)

/-- **A subgroup of `G` is determined by its graph.** -/
theorem graphOf_injOn {H H' : Subgroup (Perm Ω)} (hH : H ≤ S.G) (hH' : H' ≤ S.G)
    (h : graphOf e L H = graphOf e L H') : H = H' := by
  have key : ∀ {B B' : Subgroup (Perm Ω)}, B ≤ S.G → graphOf e L B = graphOf e L B' → B ≤ B' := by
    intro B B' hB he g hg
    have h1 : gpair e L ⟨g, hB hg⟩ ∈ graphOf e L B :=
      (mem_graphOf e L).2 ⟨g, hB hg, hg, rfl, rfl⟩
    rw [he] at h1
    obtain ⟨g', hg', hB', h1', -⟩ := (mem_graphOf e L).1 h1
    have : g' = g := (toFin e).injective h1'
    exact this ▸ hB'
  exact le_antisymm (key hH h) (key hH' h.symm)

/-- **Equal pairs of subgroups from their graph forms**: two subgroups of `G|_dom` are equal
exactly when each graph-form generating list of their lifts, encoded, lies in the group of the
other. -/
theorem eq_iff_le_gens {A A' : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hA' : A' ≤ S.domGroup) {ps ps' : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps) (hps' : PairGens e L (S.liftGroup A') ps') :
    A = A' ↔ gens (ps'.map encPair) ≤ gens (ps.map encPair) ∧
      gens (ps.map encPair) ≤ gens (ps'.map encPair) := by
  rw [gens_map_encPair, gens_map_encPair, Subgroup.map_le_map_iff_of_injective
    encPairHom_injective, Subgroup.map_le_map_iff_of_injective encPairHom_injective, ← le_antisymm_iff]
  unfold PairGens at hps hps'
  rw [hps, hps']
  constructor
  · rintro rfl; rfl
  · intro h
    exact liftGroup_injOn hA hA' (graphOf_injOn (State.liftGroup_le A) (State.liftGroup_le A')
      h.symm)

/-! ### The cache and the record -/

/-- One cache entry: the graph forms of the lifts of `A` and `N`, and the representatives on
positions (`domOfPos` gives the representatives of `G|_dom`). -/
abbrev CacheEntry (k q : ℕ) :=
  List (Perm (Fin k) × Perm (Fin q)) × List (Perm (Fin k) × Perm (Fin q)) × List (Perm (Fin k))

/-- A cache entry stands for a recorded choice. -/
def EntryOK (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S) (c : CacheEntry k L.q)
    (r : (Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom)) : Prop :=
  PairGens e L (S.liftGroup r.1.1) c.1 ∧ PairGens e L (S.liftGroup r.1.2) c.2.1 ∧
    r.1.1 ≤ S.domGroup ∧ r.1.2 ≤ S.domGroup ∧ r.2 = c.2.2.map (domOfPos e S)

/-- **The cache stands for a consistent and allowed record of representatives.** -/
def CacheOK (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S) (c : List (CacheEntry k L.q))
    (rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))) : Prop :=
  List.Forall₂ (EntryOK e S L) c rec ∧ RecordOK rec ∧ ∀ p ∈ rec, RepsOK p.1 p.2

theorem CacheOK.nil : CacheOK e S L [] [] :=
  ⟨List.Forall₂.nil, RecordOK.nil, fun _ h => by simp at h⟩

/-- What the program tests on an entry: the two pairs are equal (by `eq_iff_le_gens`). -/
def KeyMatch (c : CacheEntry k L.q) (ps ns : List (Perm (Fin k) × Perm (Fin L.q))) : Prop :=
  (gens (ps.map encPair) ≤ gens (c.1.map encPair) ∧ gens (c.1.map encPair) ≤ gens (ps.map encPair)) ∧
    (gens (ns.map encPair) ≤ gens (c.2.1.map encPair) ∧
      gens (c.2.1.map encPair) ≤ gens (ns.map encPair))

/-- An entry matches a pair exactly when its recorded pair is that pair. -/
theorem EntryOK.keyMatch_iff {c : CacheEntry k L.q}
    {r : (Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom)}
    (h : EntryOK e S L c r) {A N : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hN : N ≤ S.domGroup) {ps ns : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps) (hns : PairGens e L (S.liftGroup N) ns) :
    KeyMatch c ps ns ↔ r.1 = (A, N) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  unfold KeyMatch
  rw [← eq_iff_le_gens h3 hA h1 hps, ← eq_iff_le_gens h4 hN h2 hns, Prod.ext_iff]

/-- **A cache hit.** If the `i`-th entry matches the pair `(A, N)`, the record holds `(A, N)`
with the entry's representatives. -/
theorem CacheOK.hit {c : List (CacheEntry k L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc : CacheOK e S L c rec) {A N : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hN : N ≤ S.domGroup) {ps ns : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps) (hns : PairGens e L (S.liftGroup N) ns)
    {ent : CacheEntry k L.q} (hent : ent ∈ c) (hm : KeyMatch ent ps ns) :
    ((A, N), ent.2.2.map (domOfPos e S)) ∈ rec := by
  obtain ⟨hf, -, -⟩ := hc
  induction hf with
  | nil => simp at hent
  | @cons c₀ r₀ cs rs h₀ _ ih =>
    rcases List.mem_cons.1 hent with rfl | hent'
    · have he := (h₀.keyMatch_iff hA hN hps hns).1 hm
      have hr := h₀.2.2.2.2
      refine List.mem_cons.2 (Or.inl ?_)
      rw [← he, ← hr]
    · exact List.mem_cons_of_mem _ (ih hent')

/-- **A cache miss.** If no entry matches `(A, N)`, adding `(A, N)` with allowed representatives
keeps the cache good. -/
theorem CacheOK.miss {c : List (CacheEntry k L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc : CacheOK e S L c rec) {A N : Subgroup (Perm S.dom)} (hA : A ≤ S.domGroup)
    (hN : N ≤ S.domGroup) {ps ns : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L (S.liftGroup A) ps) (hns : PairGens e L (S.liftGroup N) ns)
    (hno : ∀ ent ∈ c, ¬ KeyMatch ent ps ns) (as : List (Perm (Fin k)))
    (hR : RepsOK (A, N) (as.map (domOfPos e S))) :
    CacheOK e S L ((ps, ns, as) :: c) (((A, N), as.map (domOfPos e S)) :: rec) := by
  obtain ⟨hf, hok, hQ⟩ := hc
  refine ⟨List.Forall₂.cons ⟨hps, hns, hA, hN, rfl⟩ hf, hok.cons_new fun p hp => ?_, ?_⟩
  · -- `p` is the record of some entry, which does not match.
    intro hpe
    obtain ⟨ent, hent, hE⟩ : ∃ ent ∈ c, EntryOK e S L ent p := by
      clear hno hok hQ
      induction hf with
      | nil => simp at hp
      | @cons c₀ r₀ cs rs h₀ _ ih =>
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact ⟨c₀, List.mem_cons_self .., h₀⟩
        · obtain ⟨ent, h1, h2⟩ := ih hp'
          exact ⟨ent, List.mem_cons_of_mem _ h1, h2⟩
    exact hno ent hent ((hE.keyMatch_iff hA hN hps hns).2 hpe)
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact hR
    · exact hQ p hp'

/-- **The representatives of a good cache**: the round's field built from the record returns the
cached representatives for every cached pair. -/
theorem CacheOK.reps_eq {c : List (CacheEntry k L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hc : CacheOK e S L c rec) (R₀ : CosetRepFn S.dom) {A N : Subgroup (Perm S.dom)}
    {l : List (Perm S.dom)} (h : ((A, N), l) ∈ rec) :
    (CosetRepFn.ofRecord R₀ rec hc.2.1 hc.2.2).reps A N = l :=
  CosetRepFn.ofRecord_reps R₀ rec hc.2.1 hc.2.2 h

end GI.Impl
