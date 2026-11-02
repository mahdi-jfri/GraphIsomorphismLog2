import Workspace.Algorithm.Tree

/-!
# The phase tree of a run (Section 7)

Lemma 7.1 is proved for an abstract tree `GI.Paper.PhaseTree` with the hypotheses
`GI.Paper.PhaseTree.Hyp`. This file builds that tree from the runs of the recursion
`GI.Algorithm.Run`, for one phase size `N`.

## Vertices

A vertex (`PNode`) is a run, or one orbit of a threshold run. The second kind expands
a fresh leaf on an intransitive domain into its orbits (Section 7.1: "Expand an
intransitive conditional query into its transitive orbit calls"); it is needed because
a branch is counted orbit by orbit, and a small intransitive remainder of an orbit
chain need not satisfy the row bound as a whole.

## Orbit forests

`Run.forest r` flattens the orbit chains of a `Continue` run into its orbit forest
(Section 7.2: "within each branch an intransitive restriction is expanded into a
disjoint orbit forest"): an orbit-chain run is replaced by the forests of its two
children, a threshold run by its orbits, and a floor reset by the forest of its
dispatcher run (Section 6.1: "Entering a column is a change of dispatcher on the
inherited state, not an additional same-domain recursive call"). Every other run is
its own forest.

## Kinds

* a threshold run, or one of its orbits: a leaf;
* an orbit-chain run: a pure orbit node whose children are its forest;
* a dispatcher reduction: one class, of row "Primitive enumeration" or "Product
  refinement", one branch per coset;
* a normalization: if the normalized group is intransitive, one class of row
  "Affected test or rectangle", one branch per coset ("its equal physical orbits have
  size at most half the parent domain, and the orbit-chain answers already have a
  physical charge"); otherwise the classes of its giant steps, one copy per coset
  ("Otherwise its immediate `GiantStep` is part of the same operation"; "All bounded
  single-factor normalization indices are included in these multiplicity bounds");
* the column step: one class of row "Row initialization or enlargement";
* an aggregation round: the inherited calls of its script, split by type into the
  rows "Affected test or rectangle" and "Visible unaffected test" (one branch per
  call), and the continuations, of row "Auxiliary-graph continuation" (one branch per
  overcoset);
* the row terminal: no inherited children (its calls are fresh).

The fresh calls (`Solve`) are not vertices: their cost belongs to the node toll.

## Result

`phaseTree_hyp`: every field of `PhaseTree.Hyp` except the cost fields `leaf_cost` and
`toll` (stage 2), for the vertices of phase size `N` (`PNode.Inv`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params} {Ω' : Type}

/-! ### Vertices -/

/-- A vertex of the phase tree on the positions `Ω`: a run, with `pt = none`, or the
orbit of the point `a` under a threshold run, with `pt = some a`. -/
structure Leaf (P : Params) (Ω : Type) where
  m : Mode
  C : Type
  S : State Ω C
  L : Option (SuppliedLabels S)
  A : Set (Perm Ω)
  run : Run P m S L A
  pt : Option Ω

/-- A vertex of the phase tree. -/
structure PNode (P : Params) where
  Ω : Type
  leaf : Leaf P Ω

namespace Leaf

variable {Ω : Type}

/-- The domain of a vertex: the active domain of the run, or the orbit. -/
def dom (ℓ : Leaf P Ω) : Set Ω :=
  match ℓ.pt with
  | none => ℓ.S.dom
  | some a => orb ℓ.S.G a

/-- The resources of a vertex. For a run they are those of its state
(`State.res`); for an orbit of a threshold run, the domain is the orbit. -/
noncomputable def state (κ : ℕ) (ℓ : Leaf P Ω) : GI.Paper.PotentialState where
  s := Nat.card ℓ.dom
  ρ := State.hierRho ℓ.S.hier
  σ := State.supSigma κ ℓ.S.G ℓ.dom
  Q := State.hierQ ℓ.S.hier
  h := ℓ.S.h

/-- The vertex of a run. -/
def ofRun {m : Mode} {C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A) :
    Leaf P Ω := ⟨m, C, S, L, A, r, none⟩

theorem ofRun_state {m : Mode} {C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (κ : ℕ) : (ofRun r).state κ = S.res κ := rfl

/-- As a vertex of the phase tree. -/
def toP (ℓ : Leaf P Ω) : PNode P := ⟨Ω, ℓ⟩

end Leaf

/-! ### Orbit representatives -/

theorem mem_orb_self (G : Subgroup (Perm Ω')) (v : Ω') : v ∈ orb G v := ⟨1, G.one_mem, rfl⟩

/-- A chosen point of the orbit of `v`; it depends only on the orbit. -/
noncomputable def orbRep (G : Subgroup (Perm Ω')) (v : Ω') : Ω' :=
  (show (orb G v).Nonempty from ⟨v, mem_orb_self G v⟩).some

open Classical in
/-- One point of each orbit of `G` in the active domain. -/
noncomputable def orbitReps {Ω C : Type} (S : State Ω C) : List Ω :=
  if h : S.dom.Finite then (h.toFinset.filter fun v => orbRep S.G v = v).toList else []

theorem orb_subset {G : Subgroup (Perm Ω')} {D : Set Ω'} (hD : Invariant G D) {v : Ω'}
    (hv : v ∈ D) : orb G v ⊆ D := by
  rintro _ ⟨g, hg, rfl⟩
  exact (hD g hg v).2 hv

theorem orb_mono {G H : Subgroup (Perm Ω')} (h : H ≤ G) (v : Ω') : orb H v ⊆ orb G v := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

theorem orb_eq_of_mem {G : Subgroup (Perm Ω')} {v w : Ω'} (hw : w ∈ orb G v) :
    orb G w = orb G v := by
  obtain ⟨g, hg, rfl⟩ := hw
  ext u
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g, G.mul_mem hk hg, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * g⁻¹, G.mul_mem hk (G.inv_mem hg), ?_⟩
    simp [Perm.mul_apply]

theorem orbRep_mem (G : Subgroup (Perm Ω')) (v : Ω') : orbRep G v ∈ orb G v :=
  Set.Nonempty.some_mem _

theorem orbRep_congr {G : Subgroup (Perm Ω')} {v w : Ω'} (h : orb G v = orb G w) :
    orbRep G v = orbRep G w := by
  unfold orbRep
  congr 1

theorem mem_orbitReps {Ω C : Type} {S : State Ω C} {a : Ω} (ha : a ∈ orbitReps S) :
    a ∈ S.dom ∧ orbRep S.G a = a := by
  classical
  unfold orbitReps at ha
  split_ifs at ha with h
  · simpa using ha
  · simp at ha

/-- The orbits of the representatives are pairwise disjoint subsets of the domain, so
their sizes add up to at most the size of the domain. -/
theorem orbitReps_sum_le {Ω C : Type} [Finite Ω] (S : State Ω C) :
    ((orbitReps S).map fun a => Nat.card (orb S.G a)).sum ≤ Nat.card S.dom := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  have h : S.dom.Finite := Set.toFinite _
  unfold orbitReps
  rw [dif_pos h, Finset.sum_map_toList]
  set F := h.toFinset.filter fun v => orbRep S.G v = v
  have hF : ∀ a ∈ F, a ∈ S.dom ∧ orbRep S.G a = a := fun a ha => by simpa [F] using ha
  have hcard : ∀ a, Nat.card (orb S.G a) = (orb S.G a).toFinset.card := fun a => by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  simp_rw [hcard]
  rw [← Finset.card_biUnion]
  · rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_biUnion, Set.mem_toFinset] at hw ⊢
    obtain ⟨a, ha, hwa⟩ := hw
    exact orb_subset S.dom_inv (hF a ha).1 hwa
  · intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hwa hwb
    simp only [Set.mem_toFinset] at hwa hwb
    apply hab
    rw [← (hF a ha).2, ← (hF b hb).2]
    exact orbRep_congr ((orb_eq_of_mem hwa).symm.trans (orb_eq_of_mem hwb))

/-! ### Orbit forests -/

/-- **The orbit forest** of a run (Section 7.2: "within each branch an intransitive
restriction is expanded into a disjoint orbit forest"). Orbit chains are flattened;
a threshold run is split into its orbits; a floor reset is replaced by the forest of
its dispatcher run. -/
noncomputable def Run.forest {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) : List (Leaf P Ω) :=
  (Run.rec (motive_1 := fun m {Ω' C'} (S : State Ω' C') L A _ => Run P m S L A → List (Leaf P Ω'))
    (motive_2 := fun _ _ _ => PUnit)
    (direct := fun _ _ self => [Leaf.ofRun self])
    (fresh := fun _ _ _ _ self => [Leaf.ofRun self])
    (threshold := @fun _ _ S _ _ _ _ self =>
      (orbitReps S).map fun a => ⟨.cont, _, S, _, _, self, some a⟩)
    (orbitStop := fun _ _ _ _ _ _ _ r₁ ih₁ _ => ih₁ r₁)
    (orbitChain := fun _ _ _ _ _ _ _ r₁ _ _ _ _ _ _ r₂ ih₁ ih₂ _ => ih₁ r₁ ++ ih₂ r₂)
    (floorReset := fun _ _ _ _ _ _ _ _ _ r ih _ => ih r)
    (dispatch := fun _ _ _ _ _ _ _ _ _ _ _ _ self => [Leaf.ofRun self])
    (normalize := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ self => [Leaf.ofRun self])
    (rowTerminal := fun _ _ _ _ _ _ _ self => [Leaf.ofRun self])
    (rowColumns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ self => [Leaf.ofRun self])
    (aggregate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ self => [Leaf.ofRun self])
    (done := fun _ => ⟨⟩)
    (ask := fun _ _ _ _ => ⟨⟩)
    r) r


/-- What a vertex of the orbit forest of a run on the state `S` inherits from `S`: the
phase, the hierarchy, a subgroup of the action on part of the domain, and a domain on
which its own group is transitive (Section 7.1: "Every eventual child is an actual
subgroup-orbit restriction of that original action and inherits its tower"). A run
vertex of a forest is never a threshold, orbit-chain or floor-reset run; an orbit
vertex comes from a threshold run. -/
structure Leaf.InForest {Ω C : Type} (ℓ : Leaf P Ω) (S : State Ω C) : Prop where
  N_eq : ℓ.S.N = S.N
  hier_eq : ℓ.S.hier = S.hier
  le : ℓ.S.G ≤ S.G
  sub : ℓ.dom ⊆ S.dom
  trans : ∀ v ∈ ℓ.dom, ℓ.dom ⊆ orb ℓ.S.G v
  ne : ℓ.dom.Nonempty
  honest : ℓ.pt = none → ℓ.run.kind ≠ .threshold ∧ ℓ.run.kind ≠ .orbitChain ∧
    ℓ.run.kind ≠ .orbitStop ∧ ℓ.run.kind ≠ .floorReset
  virt : ∀ a, ℓ.pt = some a → ℓ.run.kind = .threshold ∧ a ∈ ℓ.S.dom

theorem transitive_orb_subset {Ω C : Type} {S : State Ω C} (htr : S.Transitive) :
    ∀ v ∈ S.dom, S.dom ⊆ orb S.G v := fun v hv w hw => htr v hv w hw

theorem dom_nonempty_of_large {Ω C : Type} {S : State Ω C} {γ : ℝ}
    (hs : (S.N : ℝ) ^ γ < S.size) : S.dom.Nonempty := by
  have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpos : 0 < S.size := by exact_mod_cast h0.trans_lt hs
  have := (Nat.card_pos_iff.1 hpos).1
  exact Set.nonempty_coe_sort.1 this

/-- A transitive run that is its own forest vertex. -/
theorem inForest_self {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (htr : S.Transitive) (hne : S.dom.Nonempty)
    (hk : r.kind ≠ .threshold ∧ r.kind ≠ .orbitChain ∧ r.kind ≠ .orbitStop ∧
      r.kind ≠ .floorReset) : (Leaf.ofRun r).InForest S where
  N_eq := rfl
  hier_eq := rfl
  le := le_rfl
  sub := subset_rfl
  trans := transitive_orb_subset htr
  ne := hne
  honest := fun _ => hk
  virt := fun _ h => by simp [Leaf.ofRun] at h

theorem Leaf.InForest.mono {Ω C C' : Type} {ℓ : Leaf P Ω} {S : State Ω C}
    {T : State Ω C'} (h : ℓ.InForest T) (hN : T.N = S.N) (hhier : T.hier = S.hier)
    (hG : T.G ≤ S.G) (hD : T.dom ⊆ S.dom) : ℓ.InForest S :=
  { h with
      N_eq := h.N_eq.trans hN
      hier_eq := h.hier_eq.trans hhier
      le := h.le.trans hG
      sub := h.sub.trans hD }

/-- The facts about the forest of a run: every vertex has the mode of the run and,
when the run is not a `Solve` run, inherits from its state (`Leaf.InForest`); and the
domains of the vertices have total size at most the size of the domain. -/
theorem forest_spec :
    ∀ {m : Mode} {Ω C : Type} {S : State Ω C}
      {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)} (r : Run P m S L A),
      (∀ ℓ ∈ r.forest, ℓ.m = m) ∧ (m ≠ .solve → ∀ ℓ ∈ r.forest, ℓ.InForest S) ∧
      (Finite Ω → ((r.forest).map fun ℓ => Nat.card ℓ.dom).sum ≤ S.size) := by
  intro m Ω C S L A r
  refine Run.rec (motive_1 := fun m {Ω C} S _ A r =>
      (∀ ℓ ∈ r.forest, ℓ.m = m) ∧ (m ≠ .solve → ∀ ℓ ∈ r.forest, ℓ.InForest S) ∧
      (Finite Ω → ((r.forest).map fun ℓ => Nat.card ℓ.dom).sum ≤ S.size))
    (motive_2 := fun _ _ _ => True)
    ?direct ?fresh ?threshold ?orbitStop ?orbitChain ?floorReset ?dispatch ?normalize
    ?rowTerminal ?rowColumns ?aggregate (fun _ => trivial) (fun _ _ _ _ => trivial) r
  case direct =>
    intro Ω C S hs
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun h => absurd rfl h, fun _ => ?_⟩
    simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case fresh =>
    intro Ω C S S' A hs _ r _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun h => absurd rfl h, fun _ => ?_⟩
    simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case threshold =>
    intro Ω C S A hs r _
    refine ⟨by simp [Run.forest], fun _ => ?_, fun hfin => ?_⟩
    · intro ℓ hℓ
      simp only [Run.forest, List.mem_map] at hℓ
      obtain ⟨a, ha, rfl⟩ := hℓ
      have ha' := (mem_orbitReps ha).1
      exact
        { N_eq := rfl
          hier_eq := rfl
          le := le_rfl
          sub := orb_subset S.dom_inv ha'
          trans := fun v hv => by simp only [Leaf.dom] at hv ⊢; rw [orb_eq_of_mem hv]
          ne := ⟨a, mem_orb_self _ _⟩
          honest := fun h => by simp at h
          virt := fun b hb => by
            simp only [Option.some.injEq] at hb
            subst hb
            exact ⟨rfl, ha'⟩ }
    · have := orbitReps_sum_le S
      simpa [Run.forest, List.map_map, Function.comp_def, Leaf.dom] using this
  case orbitStop =>
    intro Ω C S S₁ D₁ hs hint hD₁ h₁ hN₁ hhier₁ _ r₁ ih₁
    obtain ⟨hG, hdom, -, -⟩ := h₁
    refine ⟨ih₁.1, fun _ ℓ hℓ => ?_, fun hfin => ?_⟩
    · exact (ih₁.2.1 (by simp) ℓ hℓ).mono hN₁ hhier₁ hG.le (hdom ▸ hD₁.subset)
    · refine (ih₁.2.2 hfin).trans ?_
      simp only [State.size, hdom, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hD₁.subset (Set.toFinite _)
  case orbitChain =>
    intro Ω C S S₁ S₂ D₁ A₁ A₂ hs hint hD₁ h₁ hN₁ hhier₁ _ r₁ t ht h₂ hN₂ hhier₂ _ r₂ ih₁ ih₂
    obtain ⟨hG₁, hdom₁, -, -⟩ := h₁
    obtain ⟨hG₂, hdom₂, -, -⟩ := h₂
    refine ⟨?_, fun _ ℓ hℓ => ?_, fun hfin => ?_⟩
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with h | h
      · exact ih₁.1 ℓ h
      · exact ih₂.1 ℓ h
    · rcases List.mem_append.1 hℓ with h | h
      · exact (ih₁.2.1 (by simp) ℓ h).mono hN₁ hhier₁ hG₁.le (hdom₁ ▸ hD₁.subset)
      · exact (ih₂.2.1 (by simp) ℓ h).mono hN₂ hhier₂ (hG₂ ▸ autGroup_le _ _ _ _)
          (hdom₂ ▸ Set.diff_subset)
    · have hsz := orbitChain_sizes hint hD₁ hdom₁ hdom₂
      have e₁ := ih₁.2.2 hfin
      have e₂ := ih₂.2.2 hfin
      change ((r₁.forest ++ r₂.forest).map fun ℓ => Nat.card ℓ.dom).sum ≤ S.size
      rw [List.map_append, List.sum_append]
      omega
  case floorReset =>
    intro Ω C S S' A hs htr hfl hcore _ _ _ hN hhier r ih
    obtain ⟨hG, hdom, -, -⟩ := hcore
    refine ⟨ih.1, fun _ ℓ hℓ => (ih.2.1 (by simp) ℓ hℓ).mono hN hhier hG.le hdom.le,
      fun hfin => ?_⟩
    have := ih.2.2 hfin
    simp only [State.size, hdom] at this ⊢
    exact this
  case dispatch =>
    intro Ω C S hs htr hfl I child _ _ _ _ A r _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun _ ℓ hℓ => ?_, fun _ => ?_⟩
    · simp only [Run.forest, List.mem_singleton] at hℓ
      subst hℓ
      exact inForest_self _ htr (dom_nonempty_of_large hs) (by simp [Run.kind])
    · simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case normalize =>
    intro Ω C _ S hs htr hfl _ _ _ _ _ _ _ _ m _ A r _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun _ ℓ hℓ => ?_, fun _ => ?_⟩
    · simp only [Run.forest, List.mem_singleton] at hℓ
      subst hℓ
      exact inForest_self _ htr (dom_nonempty_of_large hs) (by simp [Run.kind])
    · simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case rowTerminal =>
    intro Ω C S A hs htr L hrow I e _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun _ ℓ hℓ => ?_, fun _ => ?_⟩
    · simp only [Run.forest, List.mem_singleton] at hℓ
      subst hℓ
      exact inForest_self _ htr (dom_nonempty_of_large hs) (by simp [Run.kind])
    · simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case rowColumns =>
    intro Ω C S S' A hs htr L hrow I _ _ _ _ _ _ r _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun _ ℓ hℓ => ?_, fun _ => ?_⟩
    · simp only [Run.forest, List.mem_singleton] at hℓ
      subst hℓ
      exact inForest_self _ htr (dom_nonempty_of_large hs) (by simp [Run.kind])
    · simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]
  case aggregate =>
    intro Ω C S hs htr L hnot hq₀ I _ _ b e _ _ child _ _ _ _ A r _ _
    refine ⟨by simp [Run.forest, Leaf.ofRun], fun _ ℓ hℓ => ?_, fun _ => ?_⟩
    · simp only [Run.forest, List.mem_singleton] at hℓ
      subst hℓ
      exact inForest_self _ htr (dom_nonempty_of_large hs) (by simp [Run.kind])
    · simp [Run.forest, Leaf.ofRun, Leaf.dom, State.size]

/-! ### The calls of a script run -/

/-- The recursive runs of a script run are the calls of the script along the exact
answers: each satisfies every property that `Script.CallsExact` asserts, and the
`Continue` runs number `Script.numCont`. -/
theorem Exec.calls_spec {α : Type} {s : Script α} {a : α} (e : Exec P s a)
    (p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop) (hs : s.CallsExact p) :
    (∀ nd ∈ e.calls, p nd.m nd.S) ∧
      (e.calls.filter fun nd => decide (nd.m = .cont)).length = s.numCont := by
  revert hs
  refine Exec.rec (motive_1 := fun _ {_ _} _ _ _ _ => True)
    (motive_2 := fun s _ e => s.CallsExact p →
      (∀ nd ∈ e.calls, p nd.m nd.S) ∧
        (e.calls.filter fun nd => decide (nd.m = .cont)).length = s.numCont)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?done ?ask e
  case done =>
    intro α a _
    exact ⟨by simp [Exec.calls], rfl⟩
  case ask =>
    intro α Ω' C' m S k A a r e' _ ih hs
    have hA : A = S.answer := r.exact
    subst hA
    obtain ⟨hp, hk⟩ := hs
    obtain ⟨h1, h2⟩ := ih hk
    refine ⟨?_, ?_⟩
    · intro nd hnd
      change nd ∈ (⟨m, Ω', C', S, none, S.answer, r⟩ : Node P) :: e'.calls at hnd
      rcases List.mem_cons.1 hnd with rfl | h
      · exact hp
      · exact h1 nd h
    · change (((⟨m, Ω', C', S, none, S.answer, r⟩ : Node P) :: e'.calls).filter _).length = _
      rw [List.filter_cons]
      simp only [Script.numCont]
      split_ifs with hm hm' hm' <;> simp_all; omega

/-! ### The kinds of the vertices -/

open GI.Paper (Row ChildClass NodeKind PhaseTree PotentialState)

/-- The row of the table of Section 7.2 for a dispatcher reduction. -/
def DispatchKind.row : DispatchKind → Row
  | .enumeration d => .enumeration d
  | .product r => .product r

/-- The forest of a run, as vertices of the phase tree. -/
noncomputable def Run.forestP {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) : List (PNode P) :=
  r.forest.map Leaf.toP

open Classical in
/-- The branches of the inherited calls of a script run, one per `Continue` call: the
vertices of its forest whose domain has at most `θs` points (`aff = true`) or more
(`aff = false`). -/
noncomputable def callBranches (θs : ℝ) (aff : Bool) {α : Type} {s : Script α} {a : α}
    (e : Exec P s a) : List (List (PNode P)) :=
  (e.calls.filter fun nd => decide (nd.m = .cont)).map fun nd =>
    (nd.run.forest.filter fun ℓ => decide (((Nat.card ℓ.dom : ℕ) : ℝ) ≤ θs) = aff).map
      Leaf.toP

/-- The classes of children of a `GiantStep` run: the row event of the column step
(one branch), the charged calls and the continuations of an aggregation round, and
nothing for the row terminal (its calls are fresh). -/
noncomputable def giantClasses {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) : List (ChildClass (PNode P)) :=
  match r with
  | .rowColumns _ _ _ _ _ _ _ _ _ _ _ r' => [⟨.rowEvent, [r'.forestP]⟩]
  | .aggregate _ _ L _ _ _ _ _ _ e _ _ _ _ _ _ _ _ r' =>
      [⟨.affected, callBranches (P.θ * S.size) true e⟩,
        ⟨.unaffected, callBranches (P.θ * S.size) false e⟩,
        ⟨.continuation L.q, List.ofFn fun j => (r' j).forestP⟩]
  | _ => []

/-- The kind of the vertex of a run. -/
noncomputable def runKind {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) : NodeKind (PNode P) :=
  match r with
  | .direct .. => .leaf
  | .fresh .. => .leaf
  | .threshold .. => .leaf
  | .orbitStop .. => .orbit r.forestP
  | .orbitChain .. => .orbit r.forestP
  | .floorReset .. => .charged []
  | .dispatch _ _ _ I _ _ _ _ _ _ r' => .charged [⟨I.kind.row, List.ofFn fun j => (r' j).forestP⟩]
  | .normalize _ _ _ _ _ _ _ _ _ _ _ m' _ _ r' =>
      if m' = .cont then .charged [⟨.affected, List.ofFn fun j => (r' j).forestP⟩]
      else .charged (List.ofFn fun j => giantClasses (r' j)).flatten
  | .rowTerminal .. => .charged (giantClasses r)
  | .rowColumns .. => .charged (giantClasses r)
  | .aggregate .. => .charged (giantClasses r)

/-- The kind of a vertex: an orbit of a threshold run is a leaf. -/
noncomputable def PNode.rawKind (p : PNode P) : NodeKind (PNode P) :=
  match p.leaf.pt with
  | some _ => .leaf
  | none => runKind p.leaf.run

/-- A vertex of the phase with phase size `N`: finite positions, phase size `N`, not a
`Solve` run, an orbit vertex comes from a threshold run, and an orbit-chain run has
counter `h = 2` (as at a phase root, "Set `h ← 2`"; inside the phase an orbit chain is
part of the forest of its parent and is not a vertex). -/
structure PNode.Inv (N : ℕ) (p : PNode P) : Prop where
  fin : Finite p.Ω
  N_eq : p.leaf.S.N = N
  mode : p.leaf.m ≠ .solve
  virt : ∀ a, p.leaf.pt = some a → p.leaf.run.kind = .threshold ∧ a ∈ p.leaf.S.dom
  orbit_h : p.leaf.pt = none → (p.leaf.run.kind = .orbitChain ∨ p.leaf.run.kind = .orbitStop) →
    p.leaf.S.h = 2

open Classical in
/-- **The phase tree** with phase size `N`. A vertex of the phase (`PNode.Inv N`) has
the resources of its state and the kind of its run; every other vertex is an isolated
leaf with zero resources. The cost is supplied by stage 2. -/
noncomputable def phaseTree (P : Params) (N : ℕ) (cost : PNode P → ℝ) : PhaseTree (PNode P) where
  state p := if p.Inv N then p.leaf.state P.κ else ⟨0, 0, 0, 0, 0⟩
  kind p := if p.Inv N then p.rawKind else .leaf
  cost := cost

/-! ### Facts used for every class -/

/-- A run that is not a threshold, orbit-chain or floor-reset run is its own forest. -/
theorem forest_of_kind {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hk : r.kind ≠ .threshold ∧ r.kind ≠ .orbitChain ∧
      r.kind ≠ .orbitStop ∧ r.kind ≠ .floorReset) : r.forest = [Leaf.ofRun r] := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  cases r <;> first | rfl | simp [Run.kind] at h1 h2 h3 h4

/-- The resources of `X` are at most those of `Y`. -/
def ResLE (X Y : PotentialState) : Prop :=
  X.s ≤ Y.s ∧ X.ρ ≤ Y.ρ ∧ X.σ ≤ Y.σ ∧ X.Q ≤ Y.Q ∧ X.h ≤ Y.h

/-- A row's bound on a child holds for every parent with larger resources. -/
theorem row_child_mono (cc : GI.Paper.ChargingConstants) {R : Row} {X Y T : PotentialState}
    (hXY : ResLE X Y) (h : R.Child cc X T) : R.Child cc Y T := by
  obtain ⟨hs, hρ, hσ, hQ, hh⟩ := hXY
  have hs' : (X.s : ℝ) ≤ Y.s := by exact_mod_cast hs
  have hθ : 0 ≤ cc.θ := by linarith [cc.half_lt_θ]
  cases R with
  | affected =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans (mul_le_mul_of_nonneg_left hs' hθ), a2.trans hρ, a3.trans hσ, a4.trans hQ,
      by omega⟩
  | unaffected =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans hs, a2.trans hρ, by linarith, a4.trans hQ, by omega⟩
  | product r =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans hs, by linarith, a3.trans hσ, a4.trans hQ, by omega⟩
  | enumeration d =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans hs, a2.trans hρ, a3.trans hσ, a4.trans hQ, by omega⟩
  | continuation q =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans hs, a2.trans hρ, a3.trans hσ, by linarith, by omega⟩
  | rowEvent =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1.trans hs, a2.trans hρ, a3.trans hσ, a4.trans hQ, by omega⟩

/-- A row's side conditions hold for every parent with a larger domain. -/
theorem row_valid_mono (cc : GI.Paper.ChargingConstants) {R : Row} {X Y : PotentialState}
    (hs : X.s ≤ Y.s) (h : R.Valid cc X) : R.Valid cc Y := by
  cases R with
  | product r =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, h2.trans ?_⟩
    rcases Nat.eq_zero_or_pos X.s with h0 | hpos
    · exfalso
      rw [h0] at h2
      simp only [CharP.cast_eq_zero, Real.logb_zero] at h2
      have : (2 : ℝ) ≤ r := by exact_mod_cast h1
      linarith
    · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hs)
  | enumeration d => exact ⟨h.1, h.2.trans hs⟩
  | _ => exact h

/-! ### The cap update -/

theorem sum_map_set {α : Type*} (f : α → ℝ) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length) (x : α),
      ((l.set i x).map f).sum + f l[i] = (l.map f).sum + f x
  | [], _, hi, _ => absurd hi (by simp)
  | y :: l, 0, _, x => by simp; ring
  | y :: l, i + 1, hi, x => by
    have := sum_map_set f l i (by simpa using hi) x
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    linarith

/-- The cap update keeps every ratio, so it keeps `ρ`. -/
theorem CapUpdate.rho_eq {Ω : Type} {l l' : List (Interval Ω)} {q : ℕ}
    (h : CapUpdate P l q l') : State.hierRho l' = State.hierRho l := by
  obtain ⟨i, -, -, rfl⟩ := h
  have := sum_map_set (fun I : Interval Ω => ((GI.towerRank I.ratio : ℤ) : ℝ)) l i i.2
    ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩
  unfold State.hierRho
  simp only [Fin.getElem_fin] at this ⊢
  linarith

/-- **Equation `main-cap-payment`** for a cap update: `Q` drops by at least
`c_β log q`, when `βq ≥ 2`. -/
theorem CapUpdate.Q_drop {Ω : Type} {l l' : List (Interval Ω)} {q : ℕ}
    (h : CapUpdate P l q l') (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hβq : 2 ≤ P.β * q) :
    State.hierQ l' + GI.Paper.cBeta P.β * Real.log q ≤ State.hierQ l := by
  obtain ⟨i, hqc, hcd, rfl⟩ := h
  have hset := sum_map_set (fun I : Interval Ω => Real.log I.ratio * Real.log (max I.cap 2 : ℕ))
    l i i.2 ⟨l[i].part, l[i].ratio, min l[i].cap ⌊P.β * q⌋₊, l[i].origin⟩
  have hq' : (q : ℝ) ≤ l[i].cap := by exact_mod_cast hqc
  have hcd' : (l[i].cap : ℝ) ≤ l[i].ratio := by exact_mod_cast hcd
  have hnew : ((min l[i].cap ⌊P.β * q⌋₊ : ℕ) : ℝ) ≤ P.β * q := by
    have h1 : ((min l[i].cap ⌊P.β * q⌋₊ : ℕ) : ℝ) ≤ (⌊P.β * q⌋₊ : ℕ) := by
      exact_mod_cast min_le_right _ _
    exact h1.trans (Nat.floor_le (by linarith))
  obtain ⟨h1, h2⟩ := GI.Paper.eq_main_cap_payment hβ0 hβ1 hβq hq' hcd' hnew
  have hmax : ∀ c : ℕ, max (c : ℝ) 2 = ((max c 2 : ℕ) : ℝ) := fun c => by push_cast; rfl
  rw [hmax, hmax] at h1
  unfold State.hierQ GI.Paper.cBeta
  simp only [Fin.getElem_fin] at hset h1 h2 ⊢
  linarith

/-! ### The constants -/

/-- The parameters of the run agree with the constants of Section 7.5: the phase
threshold exponent is the same, and the bounds that the interfaces state with
`a, θ, κ, β, q₀` are at least as strong as those of the table. `κ ≥ 5` is the
certificate size of Lemma 4.1, and `βq₀ ≥ 2` is item (i) of Section 7.5. -/
structure Compat (P : Params) (cc : GI.Paper.ChargingConstants) : Prop where
  γ_eq : cc.γ = P.γ
  a_le : P.a ≤ cc.a
  θ_le : P.θ ≤ cc.θ
  κ_le : cc.κ ≤ P.κ
  κ_five : 5 ≤ P.κ
  β_pos : 0 < P.β
  β_le : P.β ≤ cc.β
  q₀_le : cc.q₀ ≤ P.q₀
  βq₀ : 2 ≤ P.β * P.q₀
  J_six : 6 ≤ cc.J

/-! ### Classes -/

/-- The facts of `PhaseTree.Hyp` about one class of children, at a parent with
resources `X`. -/
structure ClassOK (cc : GI.Paper.ChargingConstants) (N : ℕ) (X : PotentialState)
    (c : ChildClass (PNode P)) : Prop where
  valid : c.row.Valid cc X
  mult : (c.branches.length : ℝ) ≤ c.row.mult cc N
  inv : ∀ b ∈ c.branches, ∀ u ∈ b, u.Inv N
  pos : ∀ b ∈ c.branches, ∀ u ∈ b, 1 ≤ (u.leaf.state P.κ).s
  disj : ∀ b ∈ c.branches, (b.map fun u => (u.leaf.state P.κ).s).sum ≤ X.s
  child : ∀ b ∈ c.branches, ∀ u ∈ b, c.row.Child cc X (u.leaf.state P.κ)

theorem ClassOK.mono {cc : GI.Paper.ChargingConstants} {N : ℕ} {X Y : PotentialState}
    {c : ChildClass (PNode P)} (h : ClassOK cc N X c) (hXY : ResLE X Y) : ClassOK cc N Y c where
  valid := row_valid_mono cc hXY.1 h.valid
  mult := h.mult
  inv := h.inv
  pos := h.pos
  disj := fun b hb => (h.disj b hb).trans hXY.1
  child := fun b hb u hu => row_child_mono cc hXY (h.child b hb u hu)

theorem mem_forestP {m : Mode} {Ω C : Type} {T : State Ω C}
    {L : Option (SuppliedLabels T)} {A : Set (Perm Ω)}
    {r : Run P m T L A} {u : PNode P} (hu : u ∈ r.forestP) : ∃ ℓ ∈ r.forest, u = ℓ.toP := by
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hu
  exact ⟨ℓ, hℓ, rfl⟩

theorem Leaf.toP_inv {Ω C : Type} [Finite Ω] {ℓ : Leaf P Ω} {T : State Ω C} {N : ℕ}
    (hℓ : ℓ.InForest T) (hm : ℓ.m ≠ .solve) (hN : T.N = N) : ℓ.toP.Inv N where
  fin := ‹_›
  N_eq := hℓ.N_eq.trans hN
  mode := hm
  virt := hℓ.virt
  orbit_h := fun h hk => by
    obtain ⟨-, h2, h3, -⟩ := hℓ.honest h
    exact absurd hk (by tauto)

theorem Leaf.one_le_size {Ω C : Type} [Finite Ω] {ℓ : Leaf P Ω} {T : State Ω C}
    (hℓ : ℓ.InForest T) (κ : ℕ) : 1 ≤ (ℓ.state κ).s := by
  have := hℓ.ne.to_subtype
  exact Nat.card_pos

theorem Leaf.size_le {Ω C : Type} [Finite Ω] {ℓ : Leaf P Ω} {T : State Ω C}
    (hℓ : ℓ.InForest T) (κ : ℕ) : (ℓ.state κ).s ≤ T.size := by
  change Nat.card ℓ.dom ≤ Nat.card T.dom
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hℓ.sub (Set.toFinite _)

theorem Leaf.size_le_orb {Ω C : Type} [Finite Ω] {ℓ : Leaf P Ω} {T : State Ω C}
    (hℓ : ℓ.InForest T) (κ : ℕ) {v : Ω} (hv : v ∈ ℓ.dom) {G : Subgroup (Perm Ω)}
    (hG : ℓ.S.G ≤ G) : (ℓ.state κ).s ≤ Nat.card (orb G v) := by
  change Nat.card ℓ.dom ≤ _
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard ((hℓ.trans v hv).trans (orb_mono hG v)) (Set.toFinite _)

theorem Leaf.sigma_le {Ω C : Type} [Finite Ω] {κ : ℕ} (hκ : 5 ≤ κ) {ℓ : Leaf P Ω}
    {T : State Ω C} (hℓ : ℓ.InForest T) : ((ℓ.state κ).σ : ℝ) ≤ T.sigma κ := by
  haveI : Fintype Ω := Fintype.ofFinite Ω
  have : State.supSigma κ ℓ.S.G ℓ.dom ≤ T.sigma κ :=
    State.supSigma_le fun v hv =>
      (GI.sigma_subgroup_mono hκ v hℓ.le).trans (T.sigma_point_le κ (hℓ.sub hv))
  change ((State.supSigma κ ℓ.S.G ℓ.dom : ℕ) : ℝ) ≤ _
  exact_mod_cast this

theorem forestP_sum_le {m : Mode} {Ω C : Type} [Finite Ω] {T : State Ω C}
    {L : Option (SuppliedLabels T)}
    {A : Set (Perm Ω)} (r : Run P m T L A) (κ : ℕ) :
    (r.forestP.map fun u => (u.leaf.state κ).s).sum ≤ T.size := by
  have := (forest_spec r).2.2 ‹_›
  simpa [Run.forestP, List.map_map, Function.comp_def, Leaf.toP, Leaf.state] using this

/-- The forest of a `Continue` or `GiantStep` run on `T` as one branch: its vertices are
vertices of the phase, have nonempty domains with total size at most `|T|`, and
inherit from `T`. -/
theorem forestP_branch {m : Mode} {Ω C : Type} [Finite Ω] {T : State Ω C}
    {L : Option (SuppliedLabels T)}
    {A : Set (Perm Ω)} (r : Run P m T L A) (hm : m ≠ .solve) {N : ℕ} (hN : T.N = N) :
    ∀ u ∈ r.forestP, ∃ ℓ ∈ r.forest, u = ℓ.toP ∧ ℓ.InForest T ∧ u.Inv N ∧
      1 ≤ (u.leaf.state P.κ).s := by
  intro u hu
  obtain ⟨ℓ, hℓ, rfl⟩ := mem_forestP hu
  have hF := (forest_spec r).2.1 hm ℓ hℓ
  have hmℓ := (forest_spec r).1 ℓ hℓ
  exact ⟨ℓ, hℓ, rfl, hF, Leaf.toP_inv hF (hmℓ ▸ hm) hN, Leaf.one_le_size hF _⟩

/-! ### The inherited calls of an aggregation round -/

/-- Each branch of the inherited calls of an aggregation round comes from one charged
call `T` (`ChargedCall`): its vertices are forest vertices of a `Continue` run on `T`,
selected by the size test, with total size at most `|T|`. -/
theorem callBranches_spec {Ω C : Type} [Finite Ω] {S : State Ω C} {α : Type}
    {s : Script α} {a : α} (e : Exec P s a) (hcalls : s.CallsExact (AggCall P S))
    (θs : ℝ) (aff : Bool) :
    ∀ b ∈ callBranches θs aff e, ∃ (C' : Type) (T : State Ω C'), ChargedCall P S T ∧
      (b.map fun u => (u.leaf.state P.κ).s).sum ≤ T.size ∧
      ∀ u ∈ b, ∃ ℓ : Leaf P Ω, u = ℓ.toP ∧ ℓ.InForest T ∧ ℓ.m = .cont ∧
        decide (((Nat.card ℓ.dom : ℕ) : ℝ) ≤ θs) = aff := by
  classical
  intro b hb
  simp only [callBranches, List.mem_map, List.mem_filter] at hb
  obtain ⟨nd, ⟨hnd, hcont⟩, rfl⟩ := hb
  have hcall := (Exec.calls_spec e _ hcalls).1 nd hnd
  simp only [decide_eq_true_eq] at hcont
  rcases hcall with ⟨hm, -⟩ | ⟨-, hΩ, hT⟩
  · rw [hcont] at hm; cases hm
  obtain ⟨m', Ω', C', T, L', A', run⟩ := nd
  simp only at hΩ hT hcont ⊢
  subst hΩ hcont
  refine ⟨C', T, hT, ?_, ?_⟩
  · refine le_trans ?_ (forestP_sum_le run P.κ)
    rw [List.map_map]
    simp only [Run.forestP, List.map_map]
    apply List.Sublist.sum_le_sum ((List.filter_sublist).map _) (fun _ _ => Nat.zero_le _)
  · intro u hu
    simp only [List.mem_map, List.mem_filter] at hu
    obtain ⟨ℓ, ⟨hℓ, haff⟩, rfl⟩ := hu
    exact ⟨ℓ, rfl, (forest_spec run).2.1 (by simp) ℓ hℓ, (forest_spec run).1 ℓ hℓ,
      of_decide_eq_true haff⟩

theorem callBranches_length {α : Type} {s : Script α} {a : α} (e : Exec P s a)
    (p : ∀ {Ω' C' : Type}, Mode → State Ω' C' → Prop) (hs : s.CallsExact p) (θs : ℝ)
    (aff : Bool) : (callBranches θs aff e).length = s.numCont := by
  unfold callBranches
  rw [List.length_map]
  exact (Exec.calls_spec e p hs).2

theorem one_le_rpow_nat {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ (N : ℝ) ^ a :=
  Real.one_le_rpow (by exact_mod_cast hN) ha

theorem rpow_mono_exp {N : ℕ} (hN : 1 ≤ N) {a b : ℝ} (hab : a ≤ b) :
    (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab

/-- A run of `Continue` on a transitive state above the threshold that is not at a
column floor is its own forest. -/
theorem forest_of_transitive {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P .cont S L A) (htr : S.Transitive) (hs : (S.N : ℝ) ^ P.γ < S.size)
    (hfl : ¬ S.FloorEntered) : r.forest = [Leaf.ofRun r] := by
  apply forest_of_kind
  cases r with
  | threshold hs' => exact absurd hs' (not_le.2 hs)
  | orbitStop _ hint => exact absurd htr hint
  | orbitChain _ hint => exact absurd htr hint
  | floorReset _ _ hfl' => exact absurd hfl' hfl
  | _ => simp [Run.kind]

/-! ### The classes of a giant step -/

theorem size_le_of_subset {Ω C C' : Type} [Finite Ω] {S : State Ω C} {T : State Ω C'}
    (h : T.dom ⊆ S.dom) : T.size ≤ S.size := by
  change Nat.card T.dom ≤ Nat.card S.dom
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard h (Set.toFinite _)

/-- The resources of a child on part of the domain, under a subgroup, with the same
hierarchy, are at most those of the parent, up to the counter. -/
theorem leaf_res_le {Ω C C' : Type} [Finite Ω] {ℓ : Leaf P Ω} {T : State Ω C'}
    {S : State Ω C} (hℓ : ℓ.InForest T) (hκ : 5 ≤ P.κ) (hG : T.G ≤ S.G)
    (hD : T.dom ⊆ S.dom) :
    (ℓ.state P.κ).s ≤ T.size ∧ T.size ≤ S.size ∧
      ((ℓ.state P.κ).σ : ℝ) ≤ (S.res P.κ).σ ∧ (ℓ.state P.κ).ρ = State.hierRho T.hier ∧
      (ℓ.state P.κ).Q = State.hierQ T.hier ∧ (ℓ.state P.κ).h ≤ 2 := by
  refine ⟨Leaf.size_le hℓ _, ?_, ?_, by simp [Leaf.state, hℓ.hier_eq],
    by simp [Leaf.state, hℓ.hier_eq], ℓ.S.h_le⟩
  · change Nat.card T.dom ≤ Nat.card S.dom
    simp only [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hD (Set.toFinite _)
  · refine (Leaf.sigma_le hκ hℓ).trans ?_
    change ((T.sigma P.κ : ℕ) : ℝ) ≤ ((S.sigma P.κ : ℕ) : ℝ)
    exact_mod_cast State.sigma_le_of hκ hG hD

/-- On a forest vertex, `σ` is at most the value of the call's group at any point of
the vertex's domain (Lemma A.3 and the independence of the base point). -/
theorem leaf_sigma_le_point {Ω C' : Type} [Finite Ω] {κ : ℕ} (hκ : 5 ≤ κ) {ℓ : Leaf P Ω}
    {T : State Ω C'} (hℓ : ℓ.InForest T) {v : Ω} (hv : v ∈ ℓ.dom) :
    State.supSigma κ ℓ.S.G ℓ.dom ≤ GI.sigma κ v T.G := by
  haveI : Fintype Ω := Fintype.ofFinite Ω
  refine State.supSigma_le fun w hw => (GI.sigma_subgroup_mono hκ w hℓ.le).trans ?_
  obtain ⟨g, hg, hgw⟩ := hℓ.trans v hv hw
  exact (GI.sigma_basepoint κ T.G ⟨⟨g, hℓ.le hg⟩, hgw⟩).ge

/-- **The classes of a giant step**: at most three, and each satisfies the facts of
`PhaseTree.Hyp` at the giant step's state. -/
theorem giantClasses_ok {cc : GI.Paper.ChargingConstants} (hc : Compat P cc) {N : ℕ}
    (hN1 : 1 ≤ N) {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hSN : S.N = N) :
    (giantClasses r).length ≤ 3 ∧ ∀ c ∈ giantClasses r, ClassOK cc N (S.res P.κ) c := by
  have hκ := hc.κ_five
  cases r with
  | rowColumns hs htr L hrow I hcore hR hh1 hh hN hhier r' =>
    rename_i S'
    obtain ⟨hG, hdom, -, -⟩ := hcore
    have htr' : S'.Transitive := by
      intro v hv w hw; rw [hG, hdom] at *; exact htr v hv w hw
    have hs' : (S'.N : ℝ) ^ P.γ < S'.size := by
      rw [hN]; change _ < (Nat.card S'.dom : ℝ); rw [hdom]; exact hs
    have hfl : ¬ S'.FloorEntered := by
      rintro ⟨-, R, hR', cols, hcols, v, hv, hall⟩
      rw [hR] at hR'
      cases hR'
      simp only [Option.some.injEq] at hcols
      subst hcols
      obtain ⟨v', hv', w', hw', hne⟩ := I.proper
      rw [← hdom] at hv' hw'
      exact hne (I.cols.iseqv.trans (I.cols.iseqv.symm (hall v' hv')) (hall w' hw'))
    have hf := forest_of_transitive r' htr' hs' hfl
    refine ⟨by simp [giantClasses], fun c hc' => ?_⟩
    simp only [giantClasses, List.mem_singleton] at hc'
    subst hc'
    have hsz : S'.size = S.size := by change Nat.card S'.dom = Nat.card S.dom; rw [hdom]
    have hσ : S'.sigma P.κ = S.sigma P.κ := by
      simp only [State.sigma, hG, hdom]
    have hpos : 1 ≤ S.size := by
      have h0 : (0 : ℝ) ≤ (S.N : ℝ) ^ P.γ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have : (0 : ℝ) < S.size := h0.trans_lt hs
      exact_mod_cast this
    have hu : r'.forestP = [(Leaf.ofRun r').toP] := by simp [Run.forestP, hf]
    refine
      { valid := trivial
        mult := by simp only [List.length_singleton, Nat.cast_one, Row.mult]; exact cc.one_le_b₀
        inv := fun b hb u hu' => ?_
        pos := fun b hb u hu' => ?_
        disj := fun b hb => ?_
        child := fun b hb u hu' => ?_ } <;>
    simp only [List.mem_singleton] at hb <;> subst hb <;> (try rw [hu] at hu') <;>
      (try simp only [List.mem_singleton] at hu') <;> (try subst hu')
    · exact
        { fin := ‹_›
          N_eq := hN.trans hSN
          mode := by simp [Leaf.toP, Leaf.ofRun]
          virt := fun a h => by simp [Leaf.toP, Leaf.ofRun] at h
          orbit_h := fun _ hk => by
            have := forest_spec r'
            rw [hf] at this
            simp only [Leaf.toP, Leaf.ofRun] at hk
            cases r' <;> simp_all [Run.kind, Run.forest] }
    · change 1 ≤ S'.size; omega
    · rw [hu]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      change S'.size ≤ S.size; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change S'.size ≤ S.size; omega
      · change State.hierRho S'.hier ≤ State.hierRho S.hier; rw [hhier, hierRho_dropTriv]; exact I.rho_le
      · change ((S'.sigma P.κ : ℕ) : ℝ) ≤ ((S.sigma P.κ : ℕ) : ℝ); rw [hσ]
      · change State.hierQ S'.hier ≤ State.hierQ S.hier; rw [hhier, hierQ_dropTriv]; exact I.Q_le
      · change S'.h + 1 ≤ S.h; omega
  | aggregate hs htr L hnot hq₀ I _ _ b e τ hτ child hchild hN hhier hbk A' r' =>
    have hb := e.exact
    subst hb
    have hcalls := I.calls
    have hSN' : ((S.N : ℕ) : ℝ) = N := by rw [hSN]
    have hNa : (S.N : ℝ) ^ P.a ≤ (N : ℝ) ^ cc.a := by
      rw [hSN']; exact rpow_mono_exp hN1 hc.a_le
    have hβ1 : P.β < 1 := lt_of_le_of_lt hc.β_le cc.β_lt_one
    have hq1 : 1 ≤ L.q := by
      have : (2 : ℝ) ≤ P.β * L.q :=
        hc.βq₀.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hq₀) hc.β_pos.le)
      have : (0 : ℝ) < L.q := by nlinarith [hc.β_pos]
      exact_mod_cast this
    refine ⟨by simp [giantClasses], fun c hc' => ?_⟩
    simp only [giantClasses, List.mem_cons, List.mem_nil_iff, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · -- Affected test or rectangle.
      refine
        { valid := trivial
          mult := ?_
          inv := fun b hb u hu => ?_
          pos := fun b hb u hu => ?_
          disj := fun b hb => ?_
          child := fun b hb u hu => ?_ }
      · simp only [Row.mult]
        rw [callBranches_length e _ hcalls]
        exact I.calls_count.trans hNa
      all_goals obtain ⟨C', T, hT, hsum, hus⟩ := callBranches_spec e hcalls _ _ b hb
      · obtain ⟨ℓ, rfl, hℓ, hm, -⟩ := hus u hu
        exact Leaf.toP_inv hℓ (by rw [hm]; simp) (hT.N_eq.trans hSN)
      · obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
        exact Leaf.one_le_size hℓ _
      · exact hsum.trans (size_le_of_subset hT.sub)
      · obtain ⟨ℓ, rfl, hℓ, -, haff⟩ := hus u hu
        simp only [decide_eq_true_eq] at haff
        obtain ⟨-, -, hσ, hρ, hQ, hh⟩ := leaf_res_le hℓ hκ hT.le hT.sub
        refine ⟨?_, ?_, hσ, ?_, ?_⟩
        · change ((Nat.card ℓ.dom : ℕ) : ℝ) ≤ cc.θ * ((S.size : ℕ) : ℝ)
          refine haff.trans (mul_le_mul_of_nonneg_right hc.θ_le (Nat.cast_nonneg _))
        · change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier; rw [hρ, hT.hier_eq]
        · change (ℓ.state P.κ).Q ≤ State.hierQ S.hier; rw [hQ, hT.hier_eq]
        · change (ℓ.state P.κ).h ≤ S.h + 2; omega
    · -- Visible unaffected test.
      refine
        { valid := trivial
          mult := ?_
          inv := fun b hb u hu => ?_
          pos := fun b hb u hu => ?_
          disj := fun b hb => ?_
          child := fun b hb u hu => ?_ }
      · simp only [Row.mult]
        rw [callBranches_length e _ hcalls]
        exact I.calls_count.trans hNa
      all_goals obtain ⟨C', T, hT, hsum, hus⟩ := callBranches_spec e hcalls _ _ b hb
      · obtain ⟨ℓ, rfl, hℓ, hm, -⟩ := hus u hu
        exact Leaf.toP_inv hℓ (by rw [hm]; simp) (hT.N_eq.trans hSN)
      · obtain ⟨ℓ, rfl, hℓ, -, -⟩ := hus u hu
        exact Leaf.one_le_size hℓ _
      · exact hsum.trans (size_le_of_subset hT.sub)
      · obtain ⟨ℓ, rfl, hℓ, -, haff⟩ := hus u hu
        simp only [decide_eq_false_iff_not, not_le] at haff
        obtain ⟨hs1, hs2, -, hρ, hQ, hh⟩ := leaf_res_le hℓ hκ hT.le hT.sub
        obtain ⟨v, hv⟩ := hℓ.ne
        have hσ : State.supSigma P.κ ℓ.S.G ℓ.dom + P.κ ≤ S.sigma P.κ := by
          rcases hT.types v (hℓ.sub hv) with hsmall | hdrop
          · exfalso
            have := Leaf.size_le_orb hℓ P.κ hv hℓ.le
            have : ((Nat.card ℓ.dom : ℕ) : ℝ) ≤ Nat.card (orb T.G v) := by exact_mod_cast this
            linarith
          · exact (Nat.add_le_add_right (leaf_sigma_le_point hκ hℓ hv) _).trans hdrop
        refine ⟨hs1.trans hs2, ?_, ?_, ?_, ?_⟩
        · change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier; rw [hρ, hT.hier_eq]
        · change ((State.supSigma P.κ ℓ.S.G ℓ.dom : ℕ) : ℝ) ≤ ((S.sigma P.κ : ℕ) : ℝ) - cc.κ
          have : ((State.supSigma P.κ ℓ.S.G ℓ.dom : ℕ) : ℝ) + P.κ ≤ ((S.sigma P.κ : ℕ) : ℝ) := by
            exact_mod_cast hσ
          linarith [hc.κ_le]
        · change (ℓ.state P.κ).Q ≤ State.hierQ S.hier; rw [hQ, hT.hier_eq]
        · change (ℓ.state P.κ).h ≤ S.h + 2; omega
    · -- Auxiliary-graph continuation.
      refine
        { valid := ?_
          mult := ?_
          inv := fun b hb u hu => ?_
          pos := fun b hb u hu => ?_
          disj := fun b hb => ?_
          child := fun b hb u hu => ?_ }
      · change cc.q₀ ≤ (L.q : ℝ)
        exact hc.q₀_le.trans (by exact_mod_cast hq₀)
      · simp only [Row.mult, List.length_ofFn]
        exact I.overs_count.trans (rpow_mono_exp hq1 hc.a_le)
      all_goals
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
        obtain ⟨hGj, hdomj, -, -⟩ := hchild j
      · obtain ⟨ℓ, -, rfl, hℓ, hinv, -⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        exact hinv
      · obtain ⟨ℓ, -, rfl, -, -, hpos⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        exact hpos
      · refine (forestP_sum_le (r' j) P.κ).trans ?_
        exact size_le_of_subset hdomj.le
      · obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        have hle : (child j).G ≤ S.G := hGj ▸ I.covers.overs_le j
        obtain ⟨hs1, hs2, hσ, hρ, hQ, hh⟩ := leaf_res_le hℓ hκ hle hdomj.le
        have hcap := I.capUpdate _ (List.get_mem _ j)
        have hβq : 2 ≤ P.β * L.q :=
          hc.βq₀.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hq₀) hc.β_pos.le)
        have hdrop := hcap.Q_drop hc.β_pos hβ1 hβq
        have hcβ : GI.Paper.cBeta cc.β ≤ GI.Paper.cBeta P.β := by
          unfold GI.Paper.cBeta
          apply Real.log_le_log (by have := cc.β_lt_one; have := cc.half_lt_β; positivity)
          exact one_div_le_one_div_of_le hc.β_pos hc.β_le
        have hlogq : 0 ≤ Real.log L.q := Real.log_natCast_nonneg _
        refine ⟨hs1.trans hs2, ?_, hσ, ?_, ?_⟩
        · change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier
          rw [hρ, hhier j, hcap.rho_eq]
        · change (ℓ.state P.κ).Q ≤ State.hierQ S.hier - GI.Paper.cBeta cc.β * Real.log L.q
          rw [hQ, hhier j]
          nlinarith
        · change (ℓ.state P.κ).h ≤ S.h + 2; omega
  | _ => simp [giantClasses]

/-! ### Normal orbits -/

theorem orb_smul {Ω : Type} {G H : Subgroup (Perm Ω)} (hn : ∀ g ∈ G, ∀ k ∈ H, g * k * g⁻¹ ∈ H)
    {g : Perm Ω} (hg : g ∈ G) (v : Ω) : orb H (g v) = g '' orb H v := by
  ext w
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(g⁻¹ * k * g) v, ⟨g⁻¹ * k * g, ?_, rfl⟩, by simp [Perm.mul_apply]⟩
    have := hn g⁻¹ (G.inv_mem hg) k hk
    rwa [inv_inv] at this
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨g * k * g⁻¹, hn g hg k hk, by simp [Perm.mul_apply]⟩

/-- **The orbits of a normal subgroup of a transitive group have equal size; if there
are at least two, each has at most half the points** (Section 6.1, the single-factor
normalization: "If that preimage is intransitive, its equal physical orbits have size
at most half the parent domain"). This gives the orbit bound used for an intransitive normalization. -/
theorem normal_orbit_half {Ω C : Type} [Finite Ω] {S : State Ω C} (htr : S.Transitive)
    {G' : Subgroup (Perm Ω)} (hle : G' ≤ S.G) (hnormal : (G'.subgroupOf S.G).Normal) :
    (¬ ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ G', g v = w) →
      ∀ v ∈ S.dom, 2 * Nat.card (orb G' v) ≤ S.size := by
  intro hint v hv
  have hn : ∀ g ∈ S.G, ∀ k ∈ G', g * k * g⁻¹ ∈ G' := by
    intro g hg k hk
    have := hnormal.conj_mem ⟨k, hle hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hinv : Invariant G' S.dom := S.dom_inv.mono hle
  -- A point `w` of the domain outside the orbit of `v`.
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ S.dom, w ∉ orb G' v := by
    by_contra hall
    push Not at hall
    apply hint
    intro a ha b hb
    have ha' := hall a ha
    have hb' := hall b hb
    rw [← orb_eq_of_mem ha'] at hb'
    exact hb'
  -- The two orbits have the same size.
  obtain ⟨g, hg, rfl⟩ := htr v hv w hw
  have hcard : Nat.card (orb G' (g v)) = Nat.card (orb G' v) := by
    rw [orb_smul hn hg v, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ g.injective]
  -- They are disjoint subsets of the domain.
  have hdisj : Disjoint (orb G' v) (orb G' (g v)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hwv
    rw [← orb_eq_of_mem hx, orb_eq_of_mem hx']
    exact mem_orb_self _ _
  have hsub : orb G' v ∪ orb G' (g v) ⊆ S.dom :=
    Set.union_subset (orb_subset hinv hv) (orb_subset hinv hw)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at this
  change 2 * Nat.card (orb G' v) ≤ Nat.card S.dom
  simp only [Nat.card_coe_set_eq] at hcard ⊢
  omega

/-! ### Charged vertices -/

/-- **The classes of a charged run vertex**: at most six, and each satisfies the facts
of `PhaseTree.Hyp` at the run's state. -/
theorem runKind_charged_ok {cc : GI.Paper.ChargingConstants} (hc : Compat P cc) {N : ℕ}
    (hN2 : 2 ≤ N) {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hSN : S.N = N) {cls : List (ChildClass (PNode P))}
    (hk : runKind r = .charged cls) :
    cls.length ≤ 6 ∧ ∀ c ∈ cls, ClassOK cc N (S.res P.κ) c := by
  have hκ := hc.κ_five
  have hN1 : 1 ≤ N := by omega
  have hNa1 : 1 ≤ (N : ℝ) ^ cc.a := one_le_rpow_nat hN1 cc.a_pos.le
  cases r with
  | direct => simp [runKind] at hk
  | fresh => simp [runKind] at hk
  | threshold => simp [runKind] at hk
  | orbitStop => simp [runKind] at hk
  | orbitChain => simp [runKind] at hk
  | floorReset => simp only [runKind, NodeKind.charged.injEq] at hk; subst hk; simp
  | rowTerminal =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    obtain ⟨h1, h2⟩ := giantClasses_ok hc hN1 _ hSN
    exact ⟨by omega, h2⟩
  | rowColumns =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    obtain ⟨h1, h2⟩ := giantClasses_ok hc hN1 _ hSN
    exact ⟨by omega, h2⟩
  | aggregate =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    obtain ⟨h1, h2⟩ := giantClasses_ok hc hN1 _ hSN
    exact ⟨by omega, h2⟩
  | dispatch hs htr hfl I child hchild hN hhier _ A' r' =>
    simp only [runKind, NodeKind.charged.injEq] at hk; subst hk
    refine ⟨by simp, fun c hc' => ?_⟩
    simp only [List.mem_singleton] at hc'
    subst hc'
    have hf := I.facts
    have hbr : ∀ b ∈ List.ofFn (fun j => (r' j).forestP), ∀ u ∈ b,
        ∃ j, ∃ ℓ : Leaf P Ω, u = ℓ.toP ∧ ℓ.InForest (child j) ∧ u.Inv N ∧
          1 ≤ (u.leaf.state P.κ).s := by
      intro b hb u hu
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      obtain ⟨ℓ, -, rfl, hℓ, hinv, hpos⟩ :=
        forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
      exact ⟨j, ℓ, rfl, hℓ, hinv, hpos⟩
    have hdisj : ∀ b ∈ List.ofFn (fun j => (r' j).forestP),
        (b.map fun u => (u.leaf.state P.κ).s).sum ≤ (S.res P.κ).s := by
      intro b hb
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      exact (forestP_sum_le (r' j) P.κ).trans (size_le_of_subset (hchild j).2.1.le)
    -- The resources of a child vertex, other than the row's decrease.
    have hres : ∀ j (ℓ : Leaf P Ω), ℓ.InForest (child j) →
        (ℓ.state P.κ).s ≤ S.size ∧ ((ℓ.state P.κ).σ : ℝ) ≤ (S.res P.κ).σ ∧
        (ℓ.state P.κ).ρ = State.hierRho I.hier' ∧ (ℓ.state P.κ).Q ≤ State.hierQ S.hier ∧
        (ℓ.state P.κ).h ≤ S.h + 2 := by
      intro j ℓ hℓ
      obtain ⟨hG, hdom, -, -⟩ := hchild j
      obtain ⟨hs1, hs2, hσ, hρ, hQ, hh⟩ := leaf_res_le hℓ hκ (hG ▸ I.K_le) hdom.le
      refine ⟨hs1.trans hs2, hσ, hρ.trans (by rw [hhier j]), ?_, by omega⟩
      rw [hQ, hhier j]; exact I.Q_le
    revert hf
    generalize I.kind = k
    intro hf
    cases k with
    | enumeration d =>
      obtain ⟨hd2, hds, hn, hρ', horb⟩ := hf
      refine
        { valid := ⟨hd2, hds⟩
          mult := ?_
          inv := fun b hb u hu => (hbr b hb u hu).choose_spec.choose_spec.2.2.1
          pos := fun b hb u hu => (hbr b hb u hu).choose_spec.choose_spec.2.2.2
          disj := hdisj
          child := fun b hb u hu => ?_ }
      · simp only [DispatchKind.row, Row.mult, List.length_ofFn]
        have hexp : Real.exp (P.a * Real.log d ^ 2) ≤ Real.exp (cc.a * Real.log d ^ 2) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hc.a_le (sq_nonneg _))
        have := Real.exp_pos (cc.a * Real.log d ^ 2)
        nlinarith
      · obtain ⟨j, ℓ, rfl, hℓ, -, -⟩ := hbr b hb u hu
        obtain ⟨hs, hσ, hρ, hQ, hh⟩ := hres j ℓ hℓ
        obtain ⟨v, hv⟩ := hℓ.ne
        have hvS : v ∈ S.dom := (hchild j).2.1 ▸ hℓ.sub hv
        have h1 := Leaf.size_le_orb hℓ P.κ hv hℓ.le
        rw [(hchild j).1] at h1
        have h2 := horb v hvS
        refine ⟨?_, hρ ▸ hρ', hσ, hQ, hh⟩
        change d * Nat.card ℓ.dom ≤ S.size
        exact (Nat.mul_le_mul_left d h1).trans h2
    | product r =>
      obtain ⟨hr2, hrs, hn, hρ'⟩ := hf
      refine
        { valid := ⟨hr2, hrs⟩
          mult := ?_
          inv := fun b hb u hu => (hbr b hb u hu).choose_spec.choose_spec.2.2.1
          pos := fun b hb u hu => (hbr b hb u hu).choose_spec.choose_spec.2.2.2
          disj := hdisj
          child := fun b hb u hu => ?_ }
      · simp only [DispatchKind.row, Row.mult, List.length_ofFn]
        have hn' : (I.n : ℝ) ≤ (2 : ℝ) ^ r * (r.factorial : ℝ) := by exact_mod_cast hn
        have : (0 : ℝ) ≤ (2 : ℝ) ^ r * (r.factorial : ℝ) := by positivity
        nlinarith
      · obtain ⟨j, ℓ, rfl, hℓ, -, -⟩ := hbr b hb u hu
        obtain ⟨hs, hσ, hρ, hQ, hh⟩ := hres j ℓ hℓ
        refine ⟨hs, ?_, hσ, hQ, hh⟩
        change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier - ((r : ℝ) - 1)
        rw [hρ]; linarith
  | normalize hs htr hfl _ _ _ _ _ _ NA _ m' hmode A' r' =>
    let I := NA.I
    let child := NA.child
    have hchild : ∀ j, (child j).Inst I.G' S.dom S.x (S.y ∘ I.τ j) :=
      fun _ => ⟨rfl, rfl, rfl, rfl⟩
    have hN : ∀ j, (child j).N = S.N := fun _ => rfl
    have hhier : ∀ j, (child j).hier = I.hier' := fun _ => rfl
    simp only [runKind] at hk
    split_ifs at hk with hm'
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      refine ⟨by simp, fun c hc' => ?_⟩
      simp only [List.mem_singleton] at hc'
      subst hc'
      subst hm'
      refine
        { valid := trivial
          mult := ?_
          inv := fun b hb u hu => ?_
          pos := fun b hb u hu => ?_
          disj := fun b hb => ?_
          child := fun b hb u hu => ?_ }
      · simp only [Row.mult, List.length_ofFn]
        have hk2 : (I.k : ℝ) ≤ 2 := by exact_mod_cast I.k_le
        have : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ cc.a := rpow_mono_exp hN1 cc.one_le_a
        rw [Real.rpow_one] at this
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
        linarith
      all_goals obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      · obtain ⟨ℓ, -, rfl, -, hinv, -⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        exact hinv
      · obtain ⟨ℓ, -, rfl, -, -, hpos⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        exact hpos
      · exact (forestP_sum_le (r' j) P.κ).trans (size_le_of_subset (hchild j).2.1.le)
      · obtain ⟨ℓ, -, rfl, hℓ, -, -⟩ := forestP_branch (r' j) (by simp) ((hN j).trans hSN) u hu
        obtain ⟨hG, hdom, -, -⟩ := hchild j
        obtain ⟨hs1, hs2, hσ, hρ, hQ, hh'⟩ := leaf_res_le hℓ hκ (hG ▸ I.le) hdom.le
        obtain ⟨v, hv⟩ := hℓ.ne
        have hvS : v ∈ S.dom := hdom ▸ hℓ.sub hv
        have hint : ¬ ∀ v ∈ S.dom, ∀ w ∈ S.dom, ∃ g ∈ I.G', g v = w := by
          rcases hmode j with ⟨-, hnt⟩ | ⟨h, -⟩
          · intro hall; apply hnt; intro v hv w hw; rw [hG, hdom] at *; exact hall v hv w hw
          · cases h
        have h1 := Leaf.size_le_orb hℓ P.κ hv hℓ.le
        rw [hG] at h1
        have h2 := normal_orbit_half htr I.le I.normal hint v hvS
        refine ⟨?_, ?_, hσ, ?_, by change (ℓ.state P.κ).h ≤ S.h + 2; omega⟩
        · change ((Nat.card ℓ.dom : ℕ) : ℝ) ≤ cc.θ * ((S.size : ℕ) : ℝ)
          have h3 : 2 * Nat.card ℓ.dom ≤ S.size := (Nat.mul_le_mul_left 2 h1).trans h2
          have h4 : (2 : ℝ) * Nat.card ℓ.dom ≤ S.size := by exact_mod_cast h3
          have := cc.half_lt_θ
          have : (0 : ℝ) ≤ S.size := Nat.cast_nonneg _
          nlinarith
        · change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier; rw [hρ, hhier j]; exact I.rho_le
        · change (ℓ.state P.κ).Q ≤ State.hierQ S.hier; rw [hQ, hhier j]; exact I.Q_le
    · simp only [NodeKind.charged.injEq] at hk; subst hk
      have hgc : ∀ j, (giantClasses (r' j)).length ≤ 3 ∧
          ∀ c ∈ giantClasses (r' j), ClassOK cc N ((child j).res P.κ) c :=
        fun j => giantClasses_ok hc hN1 (r' j) ((hN j).trans hSN)
      refine ⟨?_, fun c hc' => ?_⟩
      · rw [List.length_flatten]
        calc (List.map List.length (List.ofFn fun j => giantClasses (r' j))).sum
            ≤ (List.map (fun _ => 3) (List.ofFn fun j => giantClasses (r' j))).sum := by
              apply List.sum_le_sum
              intro l hl
              obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
              exact (hgc j).1
          _ = 3 * I.k := by simp [Function.comp_def, mul_comm, I]
          _ ≤ 6 := by have := I.k_le; omega
      · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc'
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
        refine ((hgc j).2 c hcl).mono ?_
        obtain ⟨hG, hdom, -, -⟩ := hchild j
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact size_le_of_subset hdom.le
        · change State.hierRho (child j).hier ≤ State.hierRho S.hier; rw [hhier j]; exact I.rho_le
        · change (((child j).sigma P.κ : ℕ) : ℝ) ≤ ((S.sigma P.κ : ℕ) : ℝ)
          exact_mod_cast State.sigma_le_of hκ (hG ▸ I.le) hdom.le
        · change State.hierQ (child j).hier ≤ State.hierQ S.hier; rw [hhier j]; exact I.Q_le
        · change (child j).h ≤ S.h
          exact (State.restrict_h_of S I.G' I.le S.x (S.y ∘ I.τ j) I.hier' NA.keeps).le

/-! ### Orbit vertices -/

/-- The largest orbit of an intransitive state is smaller than the domain. -/
theorem LargestOrbit.size_lt {Ω C : Type} [Finite Ω] {S S₁ : State Ω C} {D₁ : Set Ω}
    (hint : ¬ S.Transitive) (hD₁ : S.LargestOrbit D₁) (h₁ : S₁.dom = D₁) :
    S₁.size < S.size := by
  have h := orbitChain_sizes (S₂ := S.inherit S.G (S.dom \ D₁)
    (S.dom_inv.diff hD₁.invariant) S.x S.y) hint hD₁ h₁ (State.inherit_dom _ _ _ _ _ _)
  omega

/-- A vertex of the forest of a run lies in the forest of one of its two orbit-chain
children, so it is no larger than that child. -/
theorem forest_mem_size_le {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) {ℓ : Leaf P Ω} (hℓ : ℓ ∈ r.forest) :
    Nat.card ℓ.dom ≤ S.size :=
  (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hℓ)).trans
    ((forest_spec r).2.2 ‹_›)

/-- **An orbit-chain vertex** with counter `2`: its forest vertices are vertices of the
phase, each nonempty and strictly smaller than the parent, with total size at most the
parent's, and with resources at most the parent's (`OrbitChild`, first case). -/
theorem runKind_orbit_ok {N : ℕ} {m : Mode} {Ω C : Type} [Finite Ω] {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) (hSN : S.N = N) (hκ : 5 ≤ P.κ)
    (hh2 : r.kind = .orbitChain ∨ r.kind = .orbitStop → S.h = 2) {cs : List (PNode P)}
    (hk : runKind r = .orbit cs) :
    (∀ u ∈ cs, u.Inv N ∧ 1 ≤ (u.leaf.state P.κ).s ∧ (u.leaf.state P.κ).s < S.size ∧
      GI.Paper.OrbitChild (S.res P.κ) (u.leaf.state P.κ)) ∧
    (cs.map fun u => (u.leaf.state P.κ).s).sum ≤ S.size := by
  -- The parts common to both orbit-chain cases.
  have common : ∀ (r : Run P .cont S L A), S.h = 2 → runKind r = .orbit r.forestP →
      (∀ ℓ ∈ r.forest, Nat.card ℓ.dom < S.size) →
      (∀ u ∈ r.forestP, u.Inv N ∧ 1 ≤ (u.leaf.state P.κ).s ∧ (u.leaf.state P.κ).s < S.size ∧
        GI.Paper.OrbitChild (S.res P.κ) (u.leaf.state P.κ)) ∧
      (r.forestP.map fun u => (u.leaf.state P.κ).s).sum ≤ S.size := by
    intro r h2 _ hlt
    refine ⟨fun u hu => ?_, forestP_sum_le r P.κ⟩
    obtain ⟨ℓ, hℓm, rfl, hℓ, hinv, hpos⟩ := forestP_branch r (by simp) hSN u hu
    obtain ⟨-, -, hσ, hρ, hQ, hh⟩ := leaf_res_le hℓ hκ le_rfl subset_rfl
    refine ⟨hinv, hpos, hlt ℓ hℓm, ?_, hσ, ?_, Or.inl ?_⟩
    · change (ℓ.state P.κ).ρ ≤ State.hierRho S.hier; rw [hρ]
    · change (ℓ.state P.κ).Q ≤ State.hierQ S.hier; rw [hQ]
    · change (ℓ.state P.κ).h ≤ S.h; rw [h2]; exact hh
  cases r with
  | orbitStop hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ =>
    simp only [runKind, NodeKind.orbit.injEq] at hk; subst hk
    refine common _ (hh2 (Or.inr rfl)) rfl fun ℓ hℓ => ?_
    exact (forest_mem_size_le r₁ hℓ).trans_lt (LargestOrbit.size_lt hint hD₁ h₁.2.1)
  | orbitChain hs hint hD₁ h₁ hN₁ hhier₁ hb₁ r₁ t ht h₂ hN₂ hhier₂ hb₂ r₂ =>
    simp only [runKind, NodeKind.orbit.injEq] at hk; subst hk
    refine common _ (hh2 (Or.inl rfl)) rfl fun ℓ hℓ => ?_
    have hsz := orbitChain_sizes hint hD₁ h₁.2.1 h₂.2.1
    rcases List.mem_append.1 hℓ with h | h
    · exact (forest_mem_size_le r₁ h).trans_lt (by omega)
    · exact (forest_mem_size_le r₂ h).trans_lt (by omega)
  | normalize => simp only [runKind] at hk; split_ifs at hk
  | _ => simp [runKind] at hk

/-! ### The hypotheses of Lemma 7.1 -/

section Hyp

variable {N : ℕ} {cost : PNode P → ℝ}

theorem phaseTree_state_of {v : PNode P} (hv : v.Inv N) :
    (phaseTree P N cost).state v = v.leaf.state P.κ := by
  simp [phaseTree, hv]

theorem phaseTree_kind_of {v : PNode P} (hv : v.Inv N) :
    (phaseTree P N cost).kind v = v.rawKind := by
  simp [phaseTree, hv]

theorem phaseTree_kind_not {v : PNode P} (hv : ¬ v.Inv N) :
    (phaseTree P N cost).kind v = .leaf := by
  simp [phaseTree, hv]

theorem two_le_of_six_le {γ : ℝ} (hγ : 0 ≤ γ) (hN6 : 6 ≤ (N : ℝ) ^ γ) : 2 ≤ N := by
  by_contra h
  have hN : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
  have := Real.rpow_le_one (Nat.cast_nonneg N) hN hγ
  linarith

theorem charged_vertex {v : PNode P} {cls : List (ChildClass (PNode P))}
    (hk : (phaseTree P N cost).kind v = .charged cls) :
    v.Inv N ∧ v.leaf.pt = none ∧ runKind v.leaf.run = .charged cls := by
  by_cases hv : v.Inv N
  · rw [phaseTree_kind_of hv] at hk
    refine ⟨hv, ?_⟩
    unfold PNode.rawKind at hk
    split at hk
    · cases hk
    · exact ⟨by assumption, hk⟩
  · rw [phaseTree_kind_not hv] at hk; cases hk

theorem orbit_vertex {v : PNode P} {cs : List (PNode P)}
    (hk : (phaseTree P N cost).kind v = .orbit cs) :
    v.Inv N ∧ v.leaf.pt = none ∧ runKind v.leaf.run = .orbit cs := by
  by_cases hv : v.Inv N
  · rw [phaseTree_kind_of hv] at hk
    refine ⟨hv, ?_⟩
    unfold PNode.rawKind at hk
    split at hk
    · cases hk
    · exact ⟨by assumption, hk⟩
  · rw [phaseTree_kind_not hv] at hk; cases hk

theorem runKind_orbit_kind {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    {r : Run P m S L A} {cs : List (PNode P)} (hk : runKind r = .orbit cs) :
    r.kind = .orbitChain ∨ r.kind = .orbitStop := by
  cases r with
  | normalize => simp only [runKind] at hk; split_ifs at hk
  | _ => simp_all [runKind, Run.kind]

theorem runKind_leaf {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)} {A : Set (Perm Ω)}
    (r : Run P m S L A) (hm : m ≠ .solve) : runKind r = .leaf ↔ r.kind = .threshold := by
  cases r with
  | normalize => simp only [runKind, Run.kind]; split_ifs <;> simp
  | _ => simp_all [runKind, Run.kind]

/-- **The hypotheses of Lemma 7.1 for the phase tree** of the runs with phase size `N`:
every field of `GI.Paper.PhaseTree.Hyp` except the cost fields `leaf_cost` and `toll`,
which are hypotheses here (stage 2). -/
theorem phaseTree_hyp {cc : GI.Paper.ChargingConstants} (hc : Compat P cc)
    (hN6 : 6 ≤ (N : ℝ) ^ cc.γ) (K : ℝ)
    (leaf_cost : ∀ v, (phaseTree P N cost).kind v = .leaf → cost v ≤ K)
    (toll : ∀ v, (phaseTree P N cost).kind v ≠ .leaf →
      cost v ≤ (N : ℝ) ^ cc.a * K + (((phaseTree P N cost).kind v).children.map cost).sum) :
    (phaseTree P N cost).Hyp cc N K := by
  have hκ := hc.κ_five
  have hN2 : 2 ≤ N := two_le_of_six_le cc.γ_pos.le hN6
  have hγ : cc.γ = P.γ := hc.γ_eq
  -- Children of charged and orbit vertices are vertices of the phase.
  have hcls : ∀ v cls, (phaseTree P N cost).kind v = .charged cls →
      cls.length ≤ 6 ∧ ∀ c ∈ cls, ClassOK cc N ((phaseTree P N cost).state v) c := by
    intro v cls hk
    obtain ⟨hv, hpt, hk'⟩ := charged_vertex hk
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    rw [phaseTree_state_of hv]
    exact runKind_charged_ok hc hN2 r hv.N_eq hk'
  have horb : ∀ v cs, (phaseTree P N cost).kind v = .orbit cs →
      (∀ u ∈ cs, u.Inv N ∧ 1 ≤ (u.leaf.state P.κ).s ∧
        (u.leaf.state P.κ).s < ((phaseTree P N cost).state v).s ∧
        GI.Paper.OrbitChild ((phaseTree P N cost).state v) (u.leaf.state P.κ)) ∧
      (cs.map fun u => (u.leaf.state P.κ).s).sum ≤ ((phaseTree P N cost).state v).s := by
    intro v cs hk
    obtain ⟨hv, hpt, hk'⟩ := orbit_vertex hk
    obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
    simp only at hpt
    subst hpt
    haveI := hv.fin
    rw [phaseTree_state_of hv]
    exact runKind_orbit_ok r hv.N_eq hκ (hv.orbit_h rfl) hk'
  have hst : ∀ u, u.Inv N → (phaseTree P N cost).state u = u.leaf.state P.κ :=
    fun u hu => phaseTree_state_of hu
  refine
    { nonneg := ?_
      leaf_small := ?_
      leaf_cost := leaf_cost
      internal_large := ?_
      toll := toll
      classes_le := ?_
      class_valid := ?_
      class_mult := ?_
      branch_pos := ?_
      branch_disjoint := ?_
      branch_child := ?_
      orbit_pos := ?_
      orbit_disjoint := ?_
      orbit_child := ?_ }
  · intro v
    by_cases hv : v.Inv N
    · rw [hst v hv]
      exact ⟨State.hierRho_nonneg _, Nat.cast_nonneg _, State.hierQ_nonneg _⟩
    · simp [phaseTree, hv]
  · intro v hk
    by_cases hv : v.Inv N
    · rw [hst v hv]
      rw [phaseTree_kind_of hv] at hk
      obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
      haveI := hv.fin
      have hthr : r.kind = .threshold → (S.size : ℝ) ≤ (N : ℝ) ^ cc.γ := by
        intro hr
        cases r <;> simp [Run.kind] at hr
        rename_i hs _
        rw [hγ, ← hv.N_eq]; exact hs
      cases pt with
      | none =>
        have : runKind r = .leaf := hk
        exact hthr ((runKind_leaf r hv.mode).1 this)
      | some a =>
        obtain ⟨hr, ha⟩ := hv.virt a rfl
        refine le_trans ?_ (hthr hr)
        change ((Nat.card (orb S.G a) : ℕ) : ℝ) ≤ ((Nat.card S.dom : ℕ) : ℝ)
        exact_mod_cast Nat.card_mono (Set.toFinite _) (orb_subset S.dom_inv ha)
    · simp only [phaseTree, if_neg hv, CharP.cast_eq_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro v hk
    by_cases hv : v.Inv N
    · rw [hst v hv]
      rw [phaseTree_kind_of hv] at hk
      obtain ⟨Ω, m, C, S, L, A, r, pt⟩ := v
      cases pt with
      | none =>
        have hk' : runKind r ≠ .leaf := hk
        have hthr : r.kind ≠ .threshold := fun h => hk' ((runKind_leaf r hv.mode).2 h)
        have := Run.internal_large r hv.mode hthr
        rw [hγ, ← hv.N_eq]
        exact this
      | some a => exact absurd rfl hk
    · exact absurd (phaseTree_kind_not hv) hk
  · intro v cls hk
    exact (hcls v cls hk).1.trans (by exact_mod_cast hc.J_six)
  · intro v cls hk c hc'
    exact ((hcls v cls hk).2 c hc').valid
  · intro v cls hk c hc'
    exact ((hcls v cls hk).2 c hc').mult
  · intro v cls hk c hc' b hb u hu
    have h := (hcls v cls hk).2 c hc'
    rw [hst u (h.inv b hb u hu)]
    exact h.pos b hb u hu
  · intro v cls hk c hc' b hb
    have h := (hcls v cls hk).2 c hc'
    rw [List.map_congr_left (fun u hu => by rw [hst u (h.inv b hb u hu)])]
    exact h.disj b hb
  · intro v cls hk c hc' b hb u hu
    have h := (hcls v cls hk).2 c hc'
    rw [hst u (h.inv b hb u hu)]
    exact h.child b hb u hu
  · intro v cs hk u hu
    obtain ⟨h1, h2, h3, -⟩ := (horb v cs hk).1 u hu
    rw [hst u h1]
    exact ⟨h2, h3⟩
  · intro v cs hk
    rw [List.map_congr_left (fun u hu => by rw [hst u ((horb v cs hk).1 u hu).1])]
    exact (horb v cs hk).2
  · intro v cs hk u hu
    obtain ⟨h1, -, -, h4⟩ := (horb v cs hk).1 u hu
    rw [hst u h1]
    exact h4

end Hyp

end GI.Algorithm
