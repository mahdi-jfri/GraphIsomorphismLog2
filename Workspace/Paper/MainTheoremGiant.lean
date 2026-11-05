module

public import Workspace.Algorithm.SupplyBuild
public import Workspace.Paper.RunExistence
public import Workspace.Paper.MainTheoremRoots

@[expose] public section

/-!
# The main theorems from the giant-step data alone

`GI.Paper.run_exists`, `thm_main_string_stage1'` and `thm_main_graph_stage1'` take the
subroutine data `Supply P`. Its `Continue` field is now built (`GI.Algorithm.Supply.ofGiant`,
`Workspace/Algorithm/SupplyBuild.lean`), so the versions below take only the giant-step data
`GiantSupply P`, with two parameter conditions:

* `γ ≥ 0`, which follows from `2α ≤ γ` and `α > 0` (Section 7.5 (ii));
* `Params.EnumeratesBounded`: `q₀! ≤ 2^⌊a log 2⌋`, so that the dispatcher enumerates every
  alternating quotient of degree at most `q₀` (Section A.3; Section 7.5 fixes `q₀` in (i) and
  then `a` in (iv), "large enough for all multiplicities").
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- `γ ≥ 0` from `2α ≤ γ`. -/
theorem γ_nonneg_of (hP : P.Terminating) (hαγ : 2 * P.α ≤ P.γ) : 0 ≤ P.γ := by
  have := hP.α_pos; linarith

/-- **The recursion terminates on every input, given the giant-step data.** -/
theorem run_exists_giant (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha : 128 ≤ P.a) (hγ : 0 ≤ P.γ) (hE : P.EnumeratesBounded) (Gs : GiantSupply P)
    {Ω C : Type} [Finite Ω] (S : State Ω C) :
    Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Equiv.Perm Ω)}, Run P .solve S none A →
        A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} :=
  run_exists hP hM ha (Supply.ofGiant hP hγ hE Gs) S

/-- **Theorem 1.2 at stage 1, for every run, given the giant-step data** (`thm:main-string`).
The hypotheses are those of `thm_main_string_stage1'`, with `GiantSupply P` and
`Params.EnumeratesBounded` in place of `Supply P`. -/
theorem thm_main_string_stage1_giant
    (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (Gs : GiantSupply P) (hκ : 64 ≤ P.κ)
    {cc : ChargingConstants} (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) :=
  thm_main_string_stage1' hP hM ha128 (Supply.ofGiant hP (γ_nonneg_of hP hαγ) hE Gs)
    hκ hc hαγ hbase hw hcw ha

/-- **Theorem 1.1 at stage 1, for every run, given the giant-step data** (`thm:main-graph`).
The hypotheses are those of `thm_main_graph_stage1'`, with `GiantSupply P` and
`Params.EnumeratesBounded` in place of `Supply P`. -/
theorem thm_main_graph_stage1_giant
    (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (hE : P.EnumeratesBounded) (Gs : GiantSupply P) (hκ : 64 ≤ P.κ)
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
  thm_main_graph_stage1' hP hM ha128 (Supply.ofGiant hP (γ_nonneg_of hP hαγ) hE Gs)
    hκ hc hαγ hbase hw hcw ha

end GI.Paper
