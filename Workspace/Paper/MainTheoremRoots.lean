module

public import Workspace.Paper.MainTheorem
public import Workspace.Paper.RootBounds
public import Workspace.Paper.ScriptCalls

@[expose] public section

/-!
# Theorems 1.1 and 1.2 at stage 1, for every run

`GI.Paper.thm_main_string_stage1` and `thm_main_graph_stage1` bound the cost of the runs with
root bounds (`Run.RootsOK`), and assume the call count `NodeBound.calls`. Both are now proved:

* every run has root bounds (`GI.Algorithm.Run.rootsOK_all`): a fresh phase starts on the
  faithful image of its domain with an initial tower (`State.FreshOf`), so eq. `main-rho`,
  eq. `main-Q` and Theorem A.9 give the bounds of `RootBounds`
  (`Workspace/Paper/RootBounds.lean`);
* every node makes at most `N^a` script calls (`GI.Algorithm.Run.scriptCalls_le`), so the work
  bounds `NodeBound'` give `NodeBound` with `af = a` (`Workspace/Paper/ScriptCalls.lean`).

The theorems below state the cost bound for every run. Compared with the unprimed versions:

* the root-bound premise `r.RootsOK cσ` and the constant `cσ` are gone; in their place is
  `κ ≥ 64` (Theorem A.9 takes `κ_cert ≥ 64`);
* the per-node hypothesis is `NodeBound' w cw` (no call count), and `af = a` with
  `a + 1 ≤ cc.a` (Section 7.4: "After increasing `a`").
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- **Theorem 1.2 at stage 1, for every run** (`thm:main-string`). There is a constant `C'`
such that for every state `S` on a finite position set, `Solve` has a run on `S`, and every run
returns the exact transporter, which is empty or a coset `t · Aut_G(x)`, at total cost at most
`exp(C' (log(s+2))²)`. -/
theorem thm_main_string_stage1' (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (Su : Supply P) (hκ : 64 ≤ P.κ) {cc : ChargingConstants}
    (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2) := by
  obtain ⟨cσ, hcσ, hok⟩ := Run.rootsOK_all hκ
  have h5 : (5 : ℝ) ≤ P.a := by linarith
  obtain ⟨C', h⟩ := thm_main_string_stage1 hP hM ha128 Su hc hαγ hbase hcσ
    (hw.toNodeBound h5) hcw (by linarith) ha
  exact ⟨C', fun S => ⟨(h S).1, fun r => ⟨((h S).2 r).1, ((h S).2 r).2 (hok r)⟩⟩⟩

/-- **Theorem 1.1 at stage 1, for every run** (`thm:main-graph`). There is a constant `C'`
such that for all graphs `X, Y` on `n` vertices, `Solve` has a run on the pair state of
Algorithm 1, and every run `r` with answer `A` gives exactly the isomorphisms from `X` to `Y`
(empty exactly when there is none, and `σ · Aut(X)` for every isomorphism `σ`), at total cost
at most `exp(C' (log(n+2))²)`. -/
theorem thm_main_graph_stage1' (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (Su : Supply P) (hκ : 64 ≤ P.κ) {cc : ChargingConstants}
    (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc)
    {w : Node P → ℝ} {cw : ℝ} (hw : NodeBound' w cw) (hcw : 0 ≤ cw) (ha : P.a + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (n : ℕ) (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj] [DecidableRel Y.Adj],
      Nonempty (Run P .solve (graphState X Y) none (graphState X Y).answer) ∧
      ∀ {A : Set (Perm (Fin n × Fin n))} (r : Run P .solve (graphState X Y) none A),
        diagonalHom (Fin n) ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
        (A = ∅ ↔ IsEmpty (X ≃g Y)) ∧
        (∀ σ : X ≃g Y, diagonalHom (Fin n) ⁻¹' A =
          (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) := by
  obtain ⟨cσ, hcσ, hok⟩ := Run.rootsOK_all hκ
  have h5 : (5 : ℝ) ≤ P.a := by linarith
  obtain ⟨C', h⟩ := thm_main_graph_stage1 hP hM ha128 Su hc hαγ hbase hcσ
    (hw.toNodeBound h5) hcw (by linarith) ha
  refine ⟨C', fun n X Y _ _ => ⟨(h n X Y).1, fun r => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := (h n X Y).2 r
  exact ⟨h1, h2, h3, h4 (hok r)⟩

end GI.Paper
