module

public import Workspace.Paper.MainTheoremGiant
public import Workspace.Algorithm.RowSupply

@[expose] public section

/-!
# The main theorems from the aggregation data alone

The giant-step data `GiantSupply P` has three cases (Algorithms 4 and 5). The two row cases
are now built (`GI.Algorithm.GiantSupply.ofAggregate`, `Workspace/Algorithm/RowSupply.lean`):
the row terminal and the column step. The versions below take only the data of the
aggregation round, for the states outside the row case, with:

* `Params.RowThreshold`: `N^α ≥ 2 max{63, 12 log₂ N} + 3` above `N₀`, so that the row case
  meets the logarithmic threshold of Theorem A.18.
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- The aggregation data: for each transitive `GiantStep` state inside a phase that is not in
the row case, with supplied labels (which carry the data of their Cameron constituent,
`SuppliedLabels`), an aggregation round whose recursive questions are asked on finite sets. -/
abbrev AggSupply (P : Params) : Type 1 :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C), S.HierInv → P.N₀ < S.N → S.size ≤ S.N →
    S.Transitive → (S.N : ℝ) ^ P.γ < S.size → (L : SuppliedLabels S) → P.q₀ < L.q →
    ¬ RowCase P.α S L →
      {I : Aggregation P S L // I.script.CallsExact fun {Ω' _} _ _ => Finite Ω'}

/-- **The recursion terminates on every input, given the aggregation data.** -/
theorem run_exists_agg
    (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive) (hT : P.RowThreshold)
    (ha : 128 ≤ P.a) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) (agg : AggSupply P)
    {Ω C : Type} [Finite Ω] (S : State Ω C) :
    Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Equiv.Perm Ω)}, Run P .solve S none A →
        A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} :=
  run_exists_giant hP hM ha hγ hE (GiantSupply.ofAggregate hT agg) S

/-- **Theorem 1.2 at stage 1, for every run, given the aggregation data** (`thm:main-string`).
The hypotheses are those of `thm_main_string_stage1_giant`, with the aggregation data and
`Params.RowThreshold` in place of `GiantSupply P`. -/
theorem thm_main_string_stage1_agg
    (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (agg : AggSupply P) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) :=
  thm_main_string_stage1_giant hP hM ha128 hE (GiantSupply.ofAggregate hT agg)
    hκ hc hαγ hbase hw hcw ha

/-- **Theorem 1.1 at stage 1, for every run, given the aggregation data** (`thm:main-graph`).
The hypotheses are those of `thm_main_graph_stage1_giant`, with the aggregation data and
`Params.RowThreshold` in place of `GiantSupply P`. -/
theorem thm_main_graph_stage1_agg
    (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (hT : P.RowThreshold)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (agg : AggSupply P) (hκ : 64 ≤ P.κ)
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
  thm_main_graph_stage1_giant hP hM ha128 hE (GiantSupply.ofAggregate hT agg)
    hκ hc hαγ hbase hw hcw ha

end GI.Paper
