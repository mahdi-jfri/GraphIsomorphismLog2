module

public import Workspace.Impl.AggCmpRep
public import Workspace.Impl.AggCertStart

@[expose] public section

/-!
# The moves of the comparison phase, for the relation `CmRep`

For each move of the step function, this file gives the program state after the move and shows
that it meets the condition of `stepOKC_of_move` for `CmRep` (`CmMvPost`): either the move
returns what the step returns, or it continues to a program state of smaller measure that stands
for a subset of the candidates. The program text (`AggCmpProg.lean`) only has to compute the
values named here.

* `cmCands_ne`: a good cache has candidates.
* `CmCacheOK.snoc`, `cmPicks_snoc`: a new entry at the end of the cache.
* `cm_resolve_hit`, `cm_resolve_miss`, `cm_resolve_empty`: the choice for a coset `A`, from the
  cache (`cmTest`: two subgroup tests and one membership test, `cm_entSet_eq_iff`).
* `cm_arrive`: a stage whose representative has been chosen.
* The moves: `cm_pair_nil_post` (end of the phase), `cm_pair_cons_rep` (start of a pair: the
  first coset), `cm_stage_end_rep` (end of a pair), `cm_stage_none_rep` (empty coset),
  `cm_stage_call` (one call), `cm_pend_rep` (the answer).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates
  Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

/-! ### The cache -/

section Cache

variable {V : Type}

/-- **A new entry at the end of a good cache.** -/
theorem CmCacheOK.snoc {ents : List (CmEnt V)} {rec : List (Set (Perm V) × Option (Perm V))}
    (h : CmCacheOK ents rec) {E : CmEnt V} (hE : ∀ E' ∈ ents, cmEntSet E' ≠ cmEntSet E) :
    CmCacheOK (ents ++ [E]) (rec ++ [cmEntRec E]) := by
  refine ⟨by rw [h.1, List.map_append]; rfl, ?_⟩
  rw [List.map_append, List.nodup_append]
  refine ⟨h.2, List.nodup_singleton _, ?_⟩
  intro a ha b hb hab
  obtain ⟨E', hE', rfl⟩ := List.mem_map.1 ha
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  exact hE E' hE' hab

/-- The candidates of a record with one more entry at the end. -/
theorem cmPicks_snoc {rec : List (Set (Perm V) × Option (Perm V))}
    (r : Set (Perm V) × Option (Perm V)) {Pk : PickFn V} :
    Pk ∈ CmPicks (rec ++ [r]) ↔ Pk ∈ CmPicks rec ∧ Pk.pick r.1 = r.2 := by
  constructor
  · intro hP
    exact ⟨fun p hp => hP p (List.mem_append_left _ hp), hP r (by simp)⟩
  · rintro ⟨hP, hr⟩ p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hP p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact hr

end Cache

section Moves

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
  {L : SuppliedLabels S} {Cs : Set (Aggregation P₀ S L.toGiantLabels)}
  {Ag₀ : Aggregation P₀ S L.toGiantLabels} {O : TestTupleOrder L.q P₀.κ}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}

/-- **A good cache has candidates.** -/
theorem cmCands_ne (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (h : CmCacheOK ents rec) : (CmCands Cs Ag₀ O rec).Nonempty := by
  obtain ⟨Pk, hP⟩ := h.nonempty
  exact ⟨{ Ag₀ with tests := O, pick := Pk }, cmHand_mem hAg₀ hsub hcl O Pk, rfl, rfl, hP⟩

/-! ### The choice of a representative -/

open Classical in
/-- **The test of a cache value** `p` against a new coset `(gs, a)`: equal groups (two subgroup
tests) and `p.2⁻¹ a` in the group (one membership test). -/
noncomputable def cmTest (gs : List (Perm (Fin k))) (a : Perm (Fin k))
    (p : List (Perm (Fin k)) × Perm (Fin k)) : Bool :=
  decide (gens gs ≤ gens p.1) && (decide (gens p.1 ≤ gens gs) && decide (p.2⁻¹ * a ∈ gens p.1))

theorem cmTest_iff {p : List (Perm (Fin k)) × Perm (Fin k)} {E' : CmEnt S.dom}
    (hp : CmEntOK e S p E') {gs : List (Perm (Fin k))} {a : Perm (Fin k)} {E : CmEnt S.dom}
    (hE : CmEntOK e S (gs, a) E) : cmTest gs a p = true ↔ cmEntSet E' = cmEntSet E := by
  rw [cm_entSet_eq_iff hp hE]
  simp only [cmTest, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨le_antisymm h2 h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1 ▸ le_rfl, h1 ▸ le_rfl, h2⟩

/-- **A hit**: the first matching value of the cache gives the representative of every
candidate. -/
theorem cm_resolve_hit {cache : List (List (Perm (Fin k)) × Perm (Fin k))}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hc : CmCacheOK ents rec) (hF : List.Forall₂ (CmEntOK e S) cache ents)
    {gs : List (Perm (Fin k))} {a : Perm (Fin k)} {E : CmEnt S.dom} (hE : CmEntOK e S (gs, a) E)
    {i : ℕ} (hi : i < cache.length) (ht : cmTest gs a cache[i] = true) :
    CmOK e (some cache[i].2) (some (domOfPos e S cache[i].2)) ∧
      ∀ Ag ∈ CmCands Cs Ag₀ O rec, Ag.pick.pick (cmEntSet E) = some (domOfPos e S cache[i].2) := by
  have hlen := hF.length_eq
  have hi' : i < ents.length := hlen ▸ hi
  have hok : CmEntOK e S cache[i] ents[i] := hF.get hi hi'
  refine ⟨⟨hok.2.2.1, rfl⟩, fun Ag hAg => ?_⟩
  have hset := (cmTest_iff hok hE).1 ht
  rw [← hset, hok.2.2.2]
  exact hc.hit (List.getElem_mem hi') rfl hAg.2.2.2

/-- **A miss**: no value of the cache matches, so the coset is new; it is appended with the
representative `a`, and the candidates are those that choose `a` for it. -/
theorem cm_resolve_miss {cache : List (List (Perm (Fin k)) × Perm (Fin k))}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hc : CmCacheOK ents rec) (hF : List.Forall₂ (CmEntOK e S) cache ents)
    {gs : List (Perm (Fin k))} {a : Perm (Fin k)} {E : CmEnt S.dom} (hE : CmEntOK e S (gs, a) E)
    (ht : ∀ p ∈ cache, cmTest gs a p = false) :
    CmCacheOK (ents ++ [E]) (rec ++ [cmEntRec E]) ∧
      List.Forall₂ (CmEntOK e S) (cache ++ [(gs, a)]) (ents ++ [E]) ∧
      CmOK e (some a) (some E.2) ∧
      CmCands Cs Ag₀ O (rec ++ [cmEntRec E]) ⊆ CmCands Cs Ag₀ O rec ∧
      ∀ Ag ∈ CmCands Cs Ag₀ O (rec ++ [cmEntRec E]), Ag.pick.pick (cmEntSet E) = some E.2 := by
  have hne : ∀ E' ∈ ents, cmEntSet E' ≠ cmEntSet E := by
    intro E' hE' heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hE'
    have hi' : i < cache.length := hF.length_eq ▸ hi
    have hok : CmEntOK e S cache[i] ents[i] := hF.get hi' hi
    have := ht _ (List.getElem_mem hi')
    rw [(cmTest_iff hok hE).2 heq] at this
    exact Bool.noConfusion this
  refine ⟨hc.snoc hne, List.rel_append hF (List.Forall₂.cons hE List.Forall₂.nil),
    ⟨hE.2.2.1, hE.2.2.2⟩, fun Ag h => ⟨h.1, h.2.1, h.2.2.1, ((cmPicks_snoc _).1 h.2.2.2).1⟩,
    fun Ag h => ((cmPicks_snoc _).1 h.2.2.2).2⟩

/-- **An empty coset** has no representative, for every candidate. -/
theorem cm_resolve_empty {rec : List (Set (Perm S.dom) × Option (Perm S.dom))} :
    ∀ Ag ∈ CmCands Cs Ag₀ O rec, Ag.pick.pick (∅ : Set (Perm S.dom)) = none :=
  fun Ag _ => cm_pick_empty Ag.pick

/-! ### Arriving at a stage -/

/-- The common form of a move that continues. -/
def CmCont (par : Val) (Bw M₀ : ℕ) (m : ℕ) (Ss : Set (Script (List Bool))) (f : ℕ)
    (st' : Val) : Prop :=
  ∃ m' Ss', m' < m ∧ Ss' ⊆ Ss ∧ CmRep e par Cs Ag₀ O πd Bw M₀ m' st' Ss' f

/-- **A stage whose representative has been chosen.** Let the candidates of `rec` be at stage
`j` of the pair `ab`, each with the representative `Pk.pick A`, and let the candidates of a
smaller good record `rec'` all choose `o` for `A`. Then the state `σ'` stands for them, at stage
`j` with `o`. -/
theorem cm_arrive {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ}
    {ps : List (CmPair L.q P₀.κ)} {j : ℕ} {A : Set (Perm S.dom)}
    {rec rec' : List (Set (Perm S.dom) × Option (Perm S.dom))} {ents' : List (CmEnt S.dom)}
    {σ' : CmSt k} {o : Option (Perm S.dom)}
    (hc : CmCacheOK ents' rec') (hF : List.Forall₂ (CmEntOK e S) σ'.cache ents')
    (hlen : ∀ p ∈ σ'.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hsub : CmCands Cs Ag₀ O rec' ⊆ CmCands Cs Ag₀ O rec)
    (hpick : ∀ Ag ∈ CmCands Cs Ag₀ O rec', Ag.pick.pick A = o) (ho : CmOK e σ'.o o)
    (hfl : σ'.fl = 1) (hacc : σ'.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps)
    (hj : σ'.j = j) (hjn : j ≤ Fintype.card S.dom)
    (hm : 2 * (ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2) < m)
    (hf : ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2 ≤ f)
    (hM : σ'.cache.length +
      2 * (ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2) ≤ M₀)
    {u : Val} (hwt : (Val.list [σ'.val par, u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAt S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.stage acc ab ps j (Ag.pick.pick A))) '' CmCands Cs Ag₀ O rec) f
      (.list [σ'.val par, u]) := by
  refine ⟨_, _, hm, ?_, ⟨.pos (.stage acc ab ps j o), σ', ents', rec', rfl, hf, hwt, hM, hc, hF,
    hlen, rfl, hfl, hacc, hdrop, hj, hjn, ho, u, rfl⟩⟩
  rintro _ ⟨Ag, hAg, rfl⟩
  refine ⟨Ag, hsub hAg, ?_⟩
  simp only [cmAtP]
  rw [hpick Ag hAg]

/-! ### The moves without calls -/

/-- **The end of the phase**: no pair is left, so the step returns the results. -/
theorem cm_pair_nil_post (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hc : CmCacheOK ents rec) (acc : List Bool) {Out : List Bool → Val → Prop} {out : Val}
    (hout : Out acc out) {Rep : Val → Set (Script (List Bool)) → ℕ → Prop} {f : ℕ}
    {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} :
    Iface.StepPostC μ Out Rep
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.pos (.pair acc ([] : List (CmPair L.q P₀.κ))))) '' CmCands Cs Ag₀ O rec) f (.list [.nat 0, out]) := by
  obtain ⟨Ag, hAg⟩ := cmCands_ne (O := O) hAg₀ hsub hcl hc
  refine Or.inl ⟨acc, out, rfl, hout, Ag, hAg, ?_⟩
  simp only [cmAtP]
  rw [cmAt_pair_nil]
  rfl

/-- **The end of a pair**: its result, then the start of the next pair. -/
theorem cm_stage_end_rep {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool}
    {ab : CmPair L.q P₀.κ} {ps : List (CmPair L.q P₀.κ)} {o : Option (Perm S.dom)}
    {σ : CmSt k} {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom)
      (.pos (.stage acc ab ps (Fintype.card S.dom) o) : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom)
      (.pos (.stage acc ab ps (Fintype.card S.dom) o) : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents) (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hacc : σ.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps) (ho : CmOK e σ.o o)
    {u : Val}
    (hwt : (Val.list [({ σ with acc := σ.acc ++ [σ.o.isSome], fl := 0 } : CmSt k).val par,
      u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.pos (.stage acc ab ps (Fintype.card S.dom) o))) '' CmCands Cs Ag₀ O rec) f
      (.list [({ σ with acc := σ.acc ++ [σ.o.isSome], fl := 0 } : CmSt k).val par, u]) := by
  have hiso : σ.o.isSome = o.isSome := by
    rcases hσ : σ.o with _ | a <;> rcases o with _ | g <;> simp_all [CmOK]
  have hps : ps = (cmPairs O).drop (acc ++ [o.isSome]).length := by
    rw [List.length_append, List.length_singleton, ← List.drop_drop, hdrop]
    rfl
  refine ⟨_, _, ?_, ?_, ⟨.pos (.pair (acc ++ [o.isSome]) ps),
    { σ with acc := σ.acc ++ [σ.o.isSome], fl := 0 }, ents, rec, rfl, ?_, hwt, ?_, hc,
    hF, hlen, rfl, rfl, by simp only; rw [hacc, hiso], hps, u, rfl⟩⟩
  · rw [hm]; simp only [cmMs]
    have := cmMeas_stage_end (S := S) (Fintype.card S.dom) acc ab ps o o.isSome
    omega
  · rintro _ ⟨Ag, hAg, rfl⟩
    exact ⟨Ag, hAg, by simp only [cmAtP]; rw [cmAt_stage_end]⟩
  · simp only [cmMc] at hmf ⊢
    have := cmMeas_stage_end (S := S) (Fintype.card S.dom) acc ab ps o o.isSome
    omega
  · simp only [cmMs] at hm ⊢
    have := cmMeas_stage_end (S := S) (Fintype.card S.dom) acc ab ps o o.isSome
    omega

/-- **An empty coset stays empty**, with no call. -/
theorem cm_stage_none_rep {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool}
    {ab : CmPair L.q P₀.κ} {ps : List (CmPair L.q P₀.κ)} {j : ℕ} (hj : j < Fintype.card S.dom)
    {σ : CmSt k} {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pos (.stage acc ab ps j none) : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pos (.stage acc ab ps j none) : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents) (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hfl : σ.fl = 1) (hacc : σ.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps)
    (hσj : σ.j = j) (ho : σ.o = none) {u : Val}
    (hwt : (Val.list [({ σ with j := σ.j + 1 } : CmSt k).val par, u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pos (.stage acc ab ps j none)))
        '' CmCands Cs Ag₀ O rec) f
      (.list [({ σ with j := σ.j + 1 } : CmSt k).val par, u]) := by
  simp only [cmMs, cmMeas] at hm
  simp only [cmMc, cmMeas] at hmf
  have hset : ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
      (.pos (.stage acc ab ps j none))) '' CmCands Cs Ag₀ O rec) =
      ((fun Ag => cmAt S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.stage acc ab ps (j + 1) (Ag.pick.pick ∅))) '' CmCands Cs Ag₀ O rec) := by
    refine Set.image_congr fun Ag _ => ?_
    simp only [cmAtP]
    rw [cm_pick_empty]
    exact cmAt_stage_none S πd _ _ _ acc ab ps hj
  rw [hset]
  have ho' : CmOK e ({ σ with j := σ.j + 1 } : CmSt k).o (none : Option (Perm S.dom)) := by
    show CmOK e σ.o none
    rw [ho]; trivial
  exact cm_arrive (σ' := { σ with j := σ.j + 1 }) (o := none) hc hF hlen subset_rfl
    (fun Ag hAg => cm_resolve_empty Ag hAg) ho' hfl hacc hdrop (by show σ.j + 1 = j + 1; omega)
    (by omega) (by omega) (by omega) (by show σ.cache.length + _ ≤ M₀; omega) hwt

/-! ### The choice for a coset -/

/-- **What the program does with a coset `A`**, for the cache `cache`: the new representative
`o'` and the new cache `cache'`. Either `A` is empty (no representative), or `A` is the coset of
an entry `(gs, a)`; then the first matching value of the cache gives the representative (a
hit), or no value matches and `(gs, a)` is appended (a miss). -/
def CmChoice (cache : List (List (Perm (Fin k)) × Perm (Fin k))) (A : Set (Perm S.dom))
    (o' : Option (Perm (Fin k))) (cache' : List (List (Perm (Fin k)) × Perm (Fin k))) : Prop :=
  (A = ∅ ∧ o' = none ∧ cache' = cache) ∨
    ∃ (gs : List (Perm (Fin k))) (a : Perm (Fin k)) (E : CmEnt S.dom), CmEntOK e S (gs, a) E ∧
      cmEntSet E = A ∧ gs.length ≤ (k + L.q) ^ 2 ∧
      ((∃ (i : ℕ) (hi : i < cache.length), cmTest gs a cache[i] = true ∧ o' = some cache[i].2 ∧
          cache' = cache) ∨
        ((∀ p ∈ cache, cmTest gs a p = false) ∧ o' = some a ∧ cache' = cache ++ [(gs, a)]))

/-- **The first match decides the choice**: with `i` the index of the first value that passes
`cmTest`, a coset of an entry gives a hit at `i` or a miss. -/
theorem cmChoice_find {cache : List (List (Perm (Fin k)) × Perm (Fin k))}
    {gs : List (Perm (Fin k))} {a : Perm (Fin k)} {E : CmEnt S.dom} (hE : CmEntOK e S (gs, a) E)
    (hl : gs.length ≤ (k + L.q) ^ 2) :
    CmChoice (e := e) (L := L) cache (cmEntSet E)
      (if cache.findIdx (cmTest gs a) < cache.length then
        some (cache.getD (cache.findIdx (cmTest gs a)) ([], 1)).2 else some a)
      (if cache.findIdx (cmTest gs a) < cache.length then cache else cache ++ [(gs, a)]) := by
  refine Or.inr ⟨gs, a, E, hE, rfl, hl, ?_⟩
  by_cases hi : cache.findIdx (cmTest gs a) < cache.length
  · refine Or.inl ⟨_, hi, List.findIdx_getElem (w := hi), ?_, by rw [if_pos hi]⟩
    rw [if_pos hi, List.getD_eq_getElem _ _ hi]
  · refine Or.inr ⟨fun p hp => ?_, by rw [if_neg hi], by rw [if_neg hi]⟩
    have hle : cache.findIdx (cmTest gs a) ≤ cache.length := List.findIdx_le_length
    have h := List.findIdx_eq_length.1 (show cache.findIdx (cmTest gs a) = cache.length by omega)
    simpa using h p hp

/-- **The choice for a coset, as a move.** Let the candidates of `rec` be at stage `j` of the
pair `ab`, each with the representative `Pk.pick A`. After the choice, the state with the new
representative and cache stands for a subset of them, at stage `j`. -/
theorem cm_choose {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ}
    {ps : List (CmPair L.q P₀.κ)} {j : ℕ} {A : Set (Perm S.dom)}
    {cache cache' : List (List (Perm (Fin k)) × Perm (Fin k))} {o' : Option (Perm (Fin k))}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hc : CmCacheOK ents rec) (hF : List.Forall₂ (CmEntOK e S) cache ents)
    (hlen : ∀ p ∈ cache, p.1.length ≤ (k + L.q) ^ 2)
    (hch : CmChoice (e := e) (L := L) cache A o' cache')
    (hdrop : (cmPairs O).drop acc.length = ab :: ps) (hjn : j ≤ Fintype.card S.dom)
    (hm : 2 * (ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2) < m)
    (hf : ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2 ≤ f)
    (hM : cache.length + 1 +
      2 * (ps.length * (Fintype.card S.dom + 2) + (Fintype.card S.dom - j) + 2) ≤ M₀)
    {u : Val} (hwt : (Val.list [(⟨j, o', cache', acc, 1⟩ : CmSt k).val par, u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAt S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.stage acc ab ps j (Ag.pick.pick A))) '' CmCands Cs Ag₀ O rec) f
      (.list [(⟨j, o', cache', acc, 1⟩ : CmSt k).val par, u]) := by
  rcases hch with ⟨hA, ho, hcc⟩ | ⟨gs, a, E, hE, hA, hgl, ⟨i, hi, ht, ho, hcc⟩ | ⟨ht, ho, hcc⟩⟩
  · subst hA o' cache'
    exact cm_arrive (σ' := ⟨j, none, cache, acc, 1⟩) (o := none) hc hF hlen subset_rfl
      (fun Ag hAg => cm_resolve_empty Ag hAg) trivial rfl rfl hdrop rfl hjn hm hf (by
        dsimp only; omega) hwt
  · subst hA o' cache'
    obtain ⟨hok, hpick⟩ := cm_resolve_hit (Cs := Cs) (Ag₀ := Ag₀) (O := O) hc hF hE hi ht
    exact cm_arrive (σ' := ⟨j, some cache[i].2, cache, acc, 1⟩) hc hF hlen subset_rfl hpick hok rfl
      rfl hdrop rfl hjn hm hf (by dsimp only; omega) hwt
  · subst hA o' cache'
    obtain ⟨hc', hF', hok, hsub, hpick⟩ := cm_resolve_miss (Cs := Cs) (Ag₀ := Ag₀) (O := O) hc hF
      hE ht
    refine cm_arrive (σ' := ⟨j, some a, cache ++ [(gs, a)], acc, 1⟩) hc' hF' ?_ hsub hpick hok rfl
      rfl hdrop rfl hjn hm hf (by dsimp only; simp only [List.length_append, List.length_singleton]; omega) hwt
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hlen p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact hgl

/-! ### The start of a pair and the answer of a call -/

/-- **The start of a pair**: the first coset, and the choice of its representative. -/
theorem cm_pair_cons_rep {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ}
    {ps : List (CmPair L.q P₀.κ)} {σ : CmSt k} {ents : List (CmEnt S.dom)}
    {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pos (.pair acc (ab :: ps)) : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pos (.pair acc (ab :: ps)) : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hdrop : (cmPairs O).drop acc.length = ab :: ps)
    {o' : Option (Perm (Fin k))} {cache' : List (List (Perm (Fin k)) × Perm (Fin k))}
    (hch : CmChoice (e := e) (L := L) σ.cache
      (lockstep S.domGroup πd 0 (dstr S (cmZ S ab.1.1)) ab.1.2 (dstr S (cmZ S ab.2.1)) ab.2.2)
      o' cache')
    {u : Val} (hwt : (Val.list [(⟨0, o', cache', acc, 1⟩ : CmSt k).val par, u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pos (.pair acc (ab :: ps))))
        '' CmCands Cs Ag₀ O rec) f
      (.list [(⟨0, o', cache', acc, 1⟩ : CmSt k).val par, u]) := by
  simp only [cmMs, cmMeas, List.length_cons] at hm
  simp only [cmMc, cmMeas, List.length_cons] at hmf
  have hset : ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
      (.pos (.pair acc (ab :: ps)))) '' CmCands Cs Ag₀ O rec) =
      ((fun Ag => cmAt S πd (dstr S S.x) (dstr S S.y) Ag.pick (.stage acc ab ps 0
        (Ag.pick.pick (lockstep S.domGroup πd 0 (dstr S (cmZ S ab.1.1)) ab.1.2
          (dstr S (cmZ S ab.2.1)) ab.2.2)))) '' CmCands Cs Ag₀ O rec) := by
    refine Set.image_congr fun Ag _ => ?_
    simp only [cmAtP]
    rw [cmAt_pair_cons, cm_strOf_dstr, cm_strOf_dstr]
  rw [hset]
  have e1 : (ps.length + 1) * (Fintype.card S.dom + 2) =
      ps.length * (Fintype.card S.dom + 2) + Fintype.card S.dom + 2 := by ring
  exact cm_choose hc hF hlen hch hdrop (Nat.zero_le _) (by omega) (by omega) (by omega) hwt

/-- **The answer of a call**: the next coset, and the choice of its representative. -/
theorem cm_pend_rep {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ}
    {ps : List (CmPair L.q P₀.κ)} {j : ℕ} {A : Set (Perm S.dom)} {σ : CmSt k}
    {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pend acc ab ps j A : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pend acc ab ps j A : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hdrop : (cmPairs O).drop acc.length = ab :: ps) (hjn : j ≤ Fintype.card S.dom)
    {o' : Option (Perm (Fin k))} {cache' : List (List (Perm (Fin k)) × Perm (Fin k))}
    (hch : CmChoice (e := e) (L := L) σ.cache A o' cache')
    {u : Val} (hwt : (Val.list [(⟨j, o', cache', acc, 1⟩ : CmSt k).val par, u]).wt ≤ Bw) :
    CmCont (e := e) (Cs := Cs) (Ag₀ := Ag₀) (O := O) (πd := πd) par Bw M₀ m
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick (.pend acc ab ps j A))
        '' CmCands Cs Ag₀ O rec) f
      (.list [(⟨j, o', cache', acc, 1⟩ : CmSt k).val par, u]) := by
  simp only [cmMs] at hm
  simp only [cmMc] at hmf
  exact cm_choose hc hF hlen hch hdrop hjn (by omega) hmf (by omega) hwt

/-- **The choice data of a first coset.** If `p` is a pair of the group generated by the graph
pairs of `G` that maps the label points of `t` to those of `t'`, and `qs` is a graph form of the
stabilizer of the label points of `t`, then the first coset is the coset of an entry that
`(first parts of qs, p.1)` stands for. -/
theorem cm_zero_ent {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)}
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {ps qs : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {κ : ℕ} (t t' : Fin κ → Fin L.q)
    (hqs : Subgroup.closure {p | p ∈ qs} =
      Subgroup.closure {p | p ∈ ps} ⊓ fixPts k L.q (cmLabPts k t))
    {p : Perm (Fin k) × Perm (Fin L.q)} (hp : encPair p ∈ gens (ps.map encPair))
    (hmap : (cmLabPts k t).map (encPair p) = cmLabPts k t') {C₀ : Type} (x y : S.dom → C₀) :
    ∃ E : CmEnt S.dom, CmEntOK e S (qs.map Prod.fst, p.1) E ∧
      cmEntSet E = lockstep S.domGroup πd 0 x t y t' := by
  have hpG : (toFin e).symm p.1 ∈ S.G := by
    obtain ⟨p', hp'', he⟩ := mem_gens_encPair.1 hp
    have := encPair_injective he
    subst this
    rw [hps] at hp''
    obtain ⟨g, hg, -, h1, -⟩ := (mem_graphOf e L).1 hp''
    rw [← h1, MulEquiv.symm_apply_apply]
    exact hg
  have hH := cm_pairGens_H0 hps t hqs
  have hgs : gens (qs.map Prod.fst) = groupFin e (cmH0 (L := L) t) := by
    ext a
    rw [mem_gens_fst hH]
    simp only [groupFin, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g, -, hA, rfl⟩; exact ⟨g, hA, rfl⟩
    · rintro ⟨g, hA, rfl⟩; exact ⟨g, cmH0_le t hA, hA, rfl⟩
  refine ⟨_, cmEntOK_of_lift (cmH0_le t) (cmKer_le_H0 πd hπ t) hgs hpG, ?_⟩
  exact (cm_zero_coset πd hπ x y t t' hpG (cm_init_mem πd hπ hps hp hmap x y)).symm

/-- **The choice data of an answer.** For the answer `u` of the call of stage `j` from `a₀`,
the next coset `a₀|_dom · B|_dom` is empty (`u = []`) or the coset of an entry that
`(gs, a₀ x)` stands for (`u = [x, ⟨gs⟩]`). -/
theorem cm_next_ent {πd : S.domGroup →* alternatingGroup (Fin L.q)} {ab : CmPair L.q P₀.κ}
    {j : ℕ} {a₀ : Perm (Fin k)} (ha₀ : (toFin e).symm a₀ ∈ S.G) {u : Val}
    (hu : AnsC e u (cmCall e πd ab j a₀).answer) :
    (u = .list [] ∧ domOfPos e S a₀ • restrictAns S (cmCall e πd ab j a₀).answer = ∅) ∨
      ∃ (x : Perm (Fin k)) (gs : List (Perm (Fin k))) (E : CmEnt S.dom),
        u = .list [encPerm x, encGroup gs] ∧ gs.length ≤ k ^ 2 ∧ CmEntOK e S (gs, a₀ * x) E ∧
        cmEntSet E = domOfPos e S a₀ • restrictAns S (cmCall e πd ab j a₀).answer := by
  rcases hu with ⟨rfl, hB⟩ | ⟨x, gs, rfl, hl, hB⟩
  · exact Or.inl ⟨rfl, cm_next_empty _ hB⟩
  · obtain ⟨E, hE, hset⟩ := cm_next_entry (e := e) (stageKer_invariant S πd _ ab.1.2 j) _ _ ha₀ hB
    exact Or.inr ⟨x, gs, E, rfl, hl, hE, hset⟩

/-! ### A call -/

/-- The parameter facts of a test tuple: its set has `κ` elements. -/
theorem cm_card_facts [Finite Ω] (t : Fin P₀.κ ↪ Fin L.q) :
    5 ≤ (tset (t : Fin P₀.κ → Fin L.q)).card ∧ P₀.κ = (tset (t : Fin P₀.κ → Fin L.q)).card ∧
      1 ≤ P₀.θ * (tset (t : Fin P₀.κ → Fin L.q)).card := by
  have hT : (tset (t : Fin P₀.κ → Fin L.q)).card = P₀.κ := by
    rw [tset, Finset.card_image_of_injective _ t.injective, Finset.card_univ, Fintype.card_fin]
  exact cp_card_facts (L := L.toGiantLabels) hT

/-- **One call**, from stage `j < n` of the pair `ab` with the kept representative of
positions `a₀`. The step returns the call with the value of `canon_compare`, and the program
state `σ` with `fl = 2`; every canonical answer `u` gives a program state of the pending stage
`j + 1`. -/
theorem cm_stage_call {Out : List Bool → Val → Prop} {c : C → ℕ} (hci : Function.Injective c) {sv : Val} (hS : Canon e c sv S)
    {hv : Val} (hh : HierValC e hv S.hier) (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {par : Val} {Bw M₀ m f : ℕ} {acc : List Bool} {ab : CmPair L.q P₀.κ}
    {ps : List (CmPair L.q P₀.κ)} {j : ℕ} (hj : j < Fintype.card S.dom) {g₀ : Perm S.dom}
    {σ : CmSt k} {ents : List (CmEnt S.dom)} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (hm : m = cmMs (Fintype.card S.dom) (.pos (.stage acc ab ps j (some g₀)) : CmPt S L.q P₀.κ))
    (hmf : cmMc (Fintype.card S.dom) (.pos (.stage acc ab ps j (some g₀)) : CmPt S L.q P₀.κ) ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hc : CmCacheOK ents rec)
    (hF : List.Forall₂ (CmEntOK e S) σ.cache ents)
    (hlen : ∀ p ∈ σ.cache, p.1.length ≤ (k + L.q) ^ 2)
    (hacc : σ.acc = acc) (hdrop : (cmPairs O).drop acc.length = ab :: ps) (hσj : σ.j = j)
    {a₀ : Perm (Fin k)} (hσo : σ.o = some a₀) (ha₀ : (toFin e).symm a₀ ∈ S.G)
    (hg₀ : domOfPos e S a₀ = g₀) {gv dv : Val}
    (hgv : GroupValC k gv (groupFin e (S.liftGroup
      (stageKer S πd (dstr S (cmZ S ab.1.1)) ab.1.2 j))))
    (hdv : DomVal e dv (Subtype.val ''
      (inc (phiT S.domGroup πd (tset ab.1.2)) (dstr S (cmZ S ab.1.1)) j : Set S.dom)))
    (hwt : ∀ u, AnsC e u (cmCall e πd ab j a₀).answer →
      (Val.list [({ σ with fl := 2 } : CmSt k).val par, u]).wt ≤ Bw) :
    Iface.StepPostC (measure P₀ .giant S) Out
      (fun st Ss f => ∃ m, CmRep e par Cs Ag₀ O πd Bw M₀ m st Ss f)
      ((fun Ag => cmAtP S πd (dstr S S.x) (dstr S S.y) Ag.pick
        (.pos (.stage acc ab ps j (some g₀)))) '' CmCands Cs Ag₀ O rec) f
      (.list [.nat 1, .nat (modeCode .cont), winVal' k gv dv
        (natList (cmCodesX e c S (cmZ S ab.1.1) (cmZ S ab.2.1) a₀))
        (natList (cmCodesY e c S (cmZ S ab.1.1) (cmZ S ab.2.1) a₀)) hv S.N,
        ({ σ with fl := 2 } : CmSt k).val par]) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨hk5, hκ, hθ⟩ := cm_card_facts ab.1.2
  set g := (toFin e).symm a₀ with hgdef
  have hga : toFin e g = a₀ := MulEquiv.apply_symm_apply _ _
  have hdh : S.domHom ⟨g, ha₀⟩ = g₀ := by rw [← hg₀, domOfPos_of_mem ha₀]
  subst hg₀
  obtain ⟨mm, hmm⟩ : ∃ mm, Fintype.card S.dom - j = mm + 1 := ⟨Fintype.card S.dom - j - 1, by omega⟩
  have hmm' : Fintype.card S.dom - (j + 1) = mm := by omega
  simp only [cmMs, cmMeas] at hm
  simp only [cmMc, cmMeas] at hmf
  have hCs : (Aggregation.pick '' CmCands Cs Ag₀ O rec).Nonempty :=
    (cmCands_ne (O := O) hAg₀ hsub hcl hc).image _
  have key := cm_call_step (z := cmZ S ab.1.1) (z' := cmZ S ab.2.1) (j := j) (m := mm) hci hS hh
    hgood htr πd ab.1.2 hk5 hκ hθ ha₀ hCs (Pk := id)
    (K := fun Pk o' => cmpPhaseFrom S πd Pk (dstr S S.x) (dstr S S.y) ps
      (cmKfin (acc ++ [o'.isSome])))
    (Out := Out) (Rep := fun st Ss f => ∃ m, CmRep e par Cs Ag₀ O πd Bw M₀ m st Ss f)
    hgv hdv (f := f) (by omega) (kst := ({ σ with fl := 2 } : CmSt k).val par) ?_
  · rw [hga, hdh] at key
    convert key using 1
    rw [Set.image_image]
    refine Set.image_congr fun Ag _ => ?_
    simp only [cmAtP, cmAt, id]
    rw [hmm, cm_strOf_dstr, cm_strOf_dstr]
  · intro u hu
    rw [hdh] at hu
    refine ⟨_, .pend acc ab ps (j + 1) (domOfPos e S a₀ • restrictAns S (cmCall e πd ab j a₀).answer),
      { σ with fl := 2 }, ents, rec, rfl, ?_, hwt u hu, ?_, hc, hF, hlen, ?_, rfl, hacc, hdrop,
      by simp only; omega, by omega, a₀, u, hσo, ha₀, by rw [hσj], by rw [hσj]; exact hu, rfl⟩
    · simp only [cmMc]; omega
    · show σ.cache.length + cmMs (Fintype.card S.dom) (CmPt.pend acc ab ps (j + 1) _ : CmPt S L.q P₀.κ) ≤ M₀
      simp only [cmMs]; omega
    · rw [Set.image_image]
      refine Set.image_congr fun Ag _ => ?_
      simp only [cmAtP, cmAt, id]
      rw [hmm', cm_strOf_dstr, cm_strOf_dstr, cmCall, domOfPos_of_mem ha₀]

end Moves

end GI.Impl
