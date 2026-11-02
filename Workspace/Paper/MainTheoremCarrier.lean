import Workspace.Paper.MainTheoremAgg
import Workspace.Paper.ScriptCalls

/-!
# The main theorems without the aggregation data

`AggSupply P` (`Workspace/Paper/MainTheoremAgg.lean`) asks for an aggregation round on every
transitive `GiantStep` state inside a phase that is not in the row case. This file builds such a
round from the state, its supplied labels and the hierarchy invariant. The carrier data of Lemma
A.30 (`CarrierSupply`) are built from the carrier invariant of the state (`State.carrier`) and
the labels above the retained columns (`Constituent.kills`), by `CarrierData.ofState`
(`carrierSupply`). So the main theorems below (`run_exists_built`,
`thm_main_string_stage1_built`, `thm_main_graph_stage1_built`) take only

* the cited results of the aggregation round (`KaryCoherentRefinement`,
  `SixTransitiveContainsAlt`, `DesignLemma`) and of the earlier versions;
* parameter conditions (`Params.Aggregates`, `Params.RowThreshold`, and those of
  `run_exists_agg`).

The earlier versions that take `CarrierSupply P` as a hypothesis are kept.

## How the fields are built

* **the selected interval** is the interval that the supplied labels carry
  (`SuppliedLabels.sel`). Its bound is at least `q` (`SuppliedLabels.le_cap`; Section 7.2: "The
  old cap is at least `q` because the selected alternating section belongs to that whole
  constituent"): this uses the cap invariant `HierInv.caps`. Its bound is at most its ratio by
  the chain condition (`SuppliedLabels.cap_le_ratio`).
* **`q ≤ N`**: the labels are read on the domain, so `Alt(q)` is a quotient of a subgroup of
  `Sym(dom)`, and `q ≤ |dom| ≤ N` (`GI.SectionCaps.permutations`).
* **`q ≥ 10`**, the other bounds and the constituent data come from the parameters
  (`q₀ ≥ 4κ + 2 ≥ 22`) and from the labels.
* **finite position sets**: the certificate and comparison phases ask only `Continue` calls,
  which are inherited calls on the same positions; the items ask `Continue` calls of the same
  kind and fresh `Solve` calls on finite sets (`AuxQuery.solve_fin`).
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- **The carrier data** of Lemma A.30 (Section 5.3: "Suppose a later column action has `q`
natural blocks and `q ≤ m`. Couple its even permutations diagonally to the same permutations of
`q` selected rows"), for each state where `AggSupply` asks for an aggregation round, when the
labels are natural and above the row threshold. -/
abbrev CarrierSupply (P : Params) : Type 1 :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
    ¬ RowCase P.α S L → (S.N : ℝ) ^ P.α < L.q → (∃ label, NaturalRows S L label) →
      CarrierData S L

/-- Labels read on the domain have degree at most the size of the domain, when `q ≥ 5`:
`Alt(q)` is then a quotient of the faithful image `G|_dom ≤ Sym(dom)`. -/
theorem _root_.GI.Algorithm.SuppliedLabels.q_le_size {Ω C : Type} [Finite Ω] {S : State Ω C} (L : SuppliedLabels S)
    (hq : 5 ≤ L.q) : L.q ≤ S.size := by
  classical
  letI : Fintype S.dom := Fintype.ofFinite _
  have h := GI.SectionCaps.quotient_degree_le (GI.SectionCaps.permutations (V := S.dom)) hq
    S.domHom L.π L.π_surj fun g hg => L.con.onDomain g hg
  rw [State.size, Nat.card_eq_fintype_card]
  exact h

/-- The labels of a giant step have degree at least `10` under the aggregation parameters:
`q > q₀ ≥ 4κ + 2` and `κ ≥ 5`. -/
theorem ten_le_of_aggregates (hA : P.Aggregates) {q : ℕ} (hq : P.q₀ < q) : 10 ≤ q := by
  have := hA.q₀_cert
  have := hA.κ_five
  omega

/-- **The data of the aggregation round of a state**, from its supplied labels, the hierarchy
invariant, the parameter conditions, the cited results and the carrier data. -/
noncomputable def _root_.GI.Algorithm.AggregationData.ofLabels {Ω C : Type} [Finite Ω] {S : State Ω C}
    (L : SuppliedLabels S) (hinv : S.HierInv) (hN : P.N₀ < S.N) (hsN : S.size ≤ S.N)
    (htr : S.Transitive) (hq : P.q₀ < L.q) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma) (hrow : ¬ RowCase P.α S L.toGiantLabels) :
    AggregationData P S L.toGiantLabels where
  sel := L.sel
  sel_cap := L.le_cap hinv htr (by have := ten_le_of_aggregates hA hq; omega)
    (L.dom_nonempty (by have := ten_le_of_aggregates hA hq; omega))
  sel_clamped := L.cap_le_ratio hinv
  q_le := (L.q_le_size (by have := ten_le_of_aggregates hA hq; omega)).trans hsN
  q_two := by have := ten_le_of_aggregates hA hq; omega
  fin := inferInstance
  htr := htr
  size_le := hsN
  params := hA
  q_large := hq
  N_large := hN
  con := L.con
  hK := JointFn.ofRefine (RefineFn.ofCited hK)
  h6 := h6
  hD := hD
  hnot := hrow

/-- **The aggregation round of a state**: the data of `AggregationData.ofLabels` with the
default source tuple and rectangle representations (`AggregationData.toAgg`). -/
noncomputable def _root_.GI.Algorithm.Aggregation.ofLabels {Ω C : Type} [Finite Ω] {S : State Ω C}
    (L : SuppliedLabels S) (hinv : S.HierInv) (hN : P.N₀ < S.N) (hsN : S.size ≤ S.N)
    (htr : S.Transitive) (hq : P.q₀ < L.q) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma) (hrow : ¬ RowCase P.α S L.toGiantLabels) :
    Aggregation P S L.toGiantLabels :=
  (AggregationData.ofLabels L hinv hN hsN htr hq hA hK h6 hD hrow).toAgg

/-- An aggregation call whose fresh `Solve` calls are on finite sets is on a finite set: its
`Continue` calls are on the parent positions. -/
theorem finite_of_aggCall {Ω C Ω' C' : Type} [Finite Ω] {S : State Ω C} {m : Mode}
    {T : State Ω' C'} (h : AggCall P S m T) (h' : m = .solve → Finite Ω') : Finite Ω' := by
  rcases h with ⟨rfl, -⟩ | ⟨-, e, -⟩
  · exact h' rfl
  · subst e; infer_instance

/-- **Every call of an aggregation round is on a finite set of positions.** -/
theorem _root_.GI.Algorithm.Aggregation.calls_finite {Ω C : Type} [Finite Ω] {S : State Ω C} {L : GiantLabels S}
    (I : Aggregation P S L) : I.script.CallsExact fun {Ω' _} _ _ => Finite Ω' := by
  classical
  letI : Fintype S.dom := Fintype.ofFinite _
  have hcont : ∀ {α : Type} {s : Script α}, s.CallsExact (AggCall P S) →
      s.CallsExact (fun m _ => m = .cont) → s.CallsExact fun {Ω' _} _ _ => Finite Ω' :=
    fun h h' => (h.and h').mono fun _ _ hT =>
      finite_of_aggCall hT.1 fun hs => by rw [hs] at hT; exact absurd hT.2 (by decide)
  refine Script.callsExact_bind _ _ (hcont I.certScript_calls ?_)
    (Script.callsExact_bind _ _ (hcont I.compScript_calls ?_)
      (Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial))
  · exact certPhase_cont S I.πd P.κ I.sets I.reps _ _
  · exact comparePhase_cont S I.πd P.κ I.tests I.pick _ _
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
    exact (((I.items b).calls (I.items_valid b)).and (I.items b).solve_finite).mono
      fun _ _ hT => finite_of_aggCall hT.1 hT.2

/-- **The carrier data, built** from the carrier invariant of the state and the labels above
the retained columns (`CarrierData.ofState`). Not in the row case, natural labels on `q > λ`
points come with retained rows of degree at least `q` (`Aggregation.rows_fit`). -/
noncomputable def carrierSupply (P : Params) : CarrierSupply P :=
  fun S _ _ _ htr _ L _ hrow hlam hnat =>
    have h : ∃ R, S.rows = some R ∧ L.q ≤ R.m := by
      by_contra h
      push Not at h
      exact hrow ⟨hlam, hnat, h⟩
    CarrierData.ofState htr L.con.kills hnat h.choose_spec.1 h.choose_spec.2

/-- **The aggregation data**, built from the supplied labels, the parameter conditions and the
cited results. -/
noncomputable def AggSupply.ofCited (hA : P.Aggregates) (hK : GI.Cited.KaryCoherentRefinement)
    (h6 : GI.Cited.SixTransitiveContainsAlt) (hD : GI.Cited.DesignLemma) : AggSupply P :=
  fun S hinv hN hsN htr _ L hq hrow =>
    let I := Aggregation.ofLabels L hinv hN hsN htr hq hA hK h6 hD hrow
    ⟨I, I.calls_finite⟩

/-- **The aggregation data from the carrier data.** The carrier data are not used any more: the
aggregation round builds them (`Aggregation.carrierData`). -/
noncomputable def AggSupply.ofCarrier (hA : P.Aggregates) (hK : GI.Cited.KaryCoherentRefinement)
    (h6 : GI.Cited.SixTransitiveContainsAlt) (hD : GI.Cited.DesignLemma)
    (_cs : CarrierSupply P) : AggSupply P :=
  AggSupply.ofCited hA hK h6 hD

/-- **The recursion terminates on every input, given the carrier data.** The hypotheses are
those of `run_exists_agg`, with the carrier data, the cited results of the aggregation round and
`Params.Aggregates` in place of `AggSupply P`. -/
theorem run_exists_carrier (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha : 128 ≤ P.a) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma) (cs : CarrierSupply P)
    {Ω C : Type} [Finite Ω] (S : State Ω C) :
    Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Equiv.Perm Ω)}, Run P .solve S none A →
        A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} :=
  run_exists_agg hP hM hcite hT ha hγ hE (AggSupply.ofCarrier hA hK h6 hD cs) S

/-- **Theorem 1.2 at stage 1, for every run, given the carrier data** (`thm:main-string`).
The hypotheses are those of `thm_main_string_stage1_agg`, with the carrier data, the cited
results of the aggregation round and `Params.Aggregates` in place of `AggSupply P`. -/
theorem thm_main_string_stage1_carrier (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma) (cs : CarrierSupply P)
    (hAut : GI.Cited.AutCardLeSq) (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) :=
  thm_main_string_stage1_agg hP hM hcite hT ha128 hE (AggSupply.ofCarrier hA hK h6 hD cs) hAut
    hLie hκ hc hαγ hbase hw hcw ha

/-- **Theorem 1.1 at stage 1, for every run, given the carrier data** (`thm:main-graph`).
The hypotheses are those of `thm_main_graph_stage1_agg`, with the carrier data, the cited
results of the aggregation round and `Params.Aggregates` in place of `AggSupply P`. -/
theorem thm_main_graph_stage1_carrier (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma) (cs : CarrierSupply P)
    (hAut : GI.Cited.AutCardLeSq) (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (n : ℕ) (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj] [DecidableRel Y.Adj],
      Nonempty (Run P .solve (graphState X Y) none (graphState X Y).answer) ∧
      ∀ {A : Set (Perm (Fin n × Fin n))} (r : Run P .solve (graphState X Y) none A),
        diagonalHom (Fin n) ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
        (A = ∅ ↔ IsEmpty (X ≃g Y)) ∧
        (∀ σ : X ≃g Y, diagonalHom (Fin n) ⁻¹' A =
          (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) :=
  thm_main_graph_stage1_agg hP hM hcite hT ha128 hE (AggSupply.ofCarrier hA hK h6 hD cs) hAut
    hLie hκ hc hαγ hbase hw hcw ha

/-- **The recursion terminates on every input** (`run_exists_carrier` with the carrier data
built, `carrierSupply`). -/
theorem run_exists_built (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha : 128 ≤ P.a) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma)
    {Ω C : Type} [Finite Ω] (S : State Ω C) :
    Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Equiv.Perm Ω)}, Run P .solve S none A →
        A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} :=
  run_exists_carrier hP hM hcite hT ha hγ hE hA hK h6 hD (carrierSupply P) S

/-- **Theorem 1.2 at stage 1, for every run** (`thm:main-string`):
`thm_main_string_stage1_carrier` with the carrier data built (`carrierSupply`). -/
theorem thm_main_string_stage1_built (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma)
    (hAut : GI.Cited.AutCardLeSq) (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) :=
  thm_main_string_stage1_carrier hP hM hcite hT ha128 hE hA hK h6 hD (carrierSupply P) hAut
    hLie hκ hc hαγ hbase hw hcw ha

/-- **Theorem 1.1 at stage 1, for every run** (`thm:main-graph`):
`thm_main_graph_stage1_carrier` with the carrier data built (`carrierSupply`). -/
theorem thm_main_graph_stage1_built (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hcite : GI.Cited.TransitiveAffected) (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (hA : P.Aggregates)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hD : GI.Cited.DesignLemma)
    (hAut : GI.Cited.AutCardLeSq) (hLie : GI.Cited.SimpleValuationDegree) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (n : ℕ) (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj] [DecidableRel Y.Adj],
      Nonempty (Run P .solve (graphState X Y) none (graphState X Y).answer) ∧
      ∀ {A : Set (Perm (Fin n × Fin n))} (r : Run P .solve (graphState X Y) none A),
        diagonalHom (Fin n) ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
        (A = ∅ ↔ IsEmpty (X ≃g Y)) ∧
        (∀ σ : X ≃g Y, diagonalHom (Fin n) ⁻¹' A =
          (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) :=
  thm_main_graph_stage1_carrier hP hM hcite hT ha128 hE hA hK h6 hD (carrierSupply P) hAut
    hLie hκ hc hαγ hbase hw hcw ha

end GI.Paper
