import Workspace.Paper.PhaseCost
import Workspace.Paper.RunExistence

/-!
# Theorems 1.1 and 1.2 at stage 1

This file assembles the main results of the paper for the abstract recursion
`GI.Algorithm.Run` (stage 1).

* `GI.Paper.eq_main_recurrence`: eq. `main-recurrence`,
  `F(N) ≤ exp(C (log(N+2))²) (1 + F(⌈N^γ⌉))`, for the worst-case cost
  `F = GI.Algorithm.worstCost` (Section 7.4).
* `GI.Paper.main_recurrence_solved`: `F(N) ≤ exp(C' (log(N+2))²)`.
* `GI.Paper.thm_main_string_stage1`: Theorem 1.2 at stage 1.
* `GI.Paper.thm_main_graph_stage1`: Theorem 1.1 at stage 1.

## What the theorems assume

Their hypotheses are what stage 2 must provide, together with the parameters and the
cited results:

* the parameters: `P.Terminating` and `2α ≤ γ` (eq. `scale-constraints`), constants `cc`
  of Section 7.5 compatible with `P` (`GI.Algorithm.Compat`), and `N₀` above the base size
  of Section 7.5 (`AboveBase`);
* existence of runs: the subroutine data `GI.Algorithm.Supply`, Maróti's theorem
  (`GI.Cited.MarotiPrimitive`, an axiom) and `a ≥ 128` (as in `GI.Paper.run_exists`);
* the per-node hypothesis `GI.Algorithm.NodeBound w cw af` on the work `w` of the nodes,
  with `af + 1 ≤ a` (Section 7.4: "After increasing `a`");
* the runs that stage 2 builds have root bounds (`GI.Algorithm.Run.RootsOK cσ`): the
  cost bound is stated for these runs.

The cost of a run is its total cost `GI.Algorithm.Run.total w`, the sum of `w` over its
nodes. Stage 2 must show that its machine cost is at most a polynomial in this total
cost and the input size.

## Generators

At stage 1 an answer is a set of permutations: the empty set or a coset `t · Aut`. The
graph theorem returns one isomorphism `σ` and the subgroup `Aut(X)` with
`answer = σ · Aut(X)`. Stage 2 must represent the answer by `σ` and a list of generators
of `Aut(X)` (Section 3: "Every fresh call uses the faithful permutation image on its
own active domain, with a polynomial-size strong generating set"), which is the output
format of `GI.Statement.CorrectOutput`.
-/

namespace GI.Paper

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {P : Params}

/-- **`N₀` is above the base size** of Section 7.5: for every phase size `n > N₀`,
`n^γ ≥ 6` and `n^{γD-a} ≥ 2` (the hypotheses of Lemma 7.1), and `⌈n^γ⌉ < n` (a fresh call
of the threshold is smaller than the phase). Section 7.4: "above an absolute base
size". -/
def AboveBase (P : Params) (cc : ChargingConstants) : Prop :=
  ∀ n : ℕ, P.N₀ < n →
    6 ≤ (n : ℝ) ^ cc.γ ∧ 2 ≤ (n : ℝ) ^ (cc.γ * cc.D - cc.a) ∧ ⌈(n : ℝ) ^ P.γ⌉₊ < n

section Recurrence

variable {cc : ChargingConstants} {cσ : ℝ} {w : Node P → ℝ} {cw af : ℝ}

/-- **Equation `main-recurrence`** (Section 7.4), for the worst-case cost
`F = worstCost w cσ` of the runs with root bounds: `F(N)` is finite (`BddAbove`) and
`F(N) ≤ exp(C (log(N+2))²) (1 + F(⌈N^γ⌉))` for every `N`. Below the base size every run is
a direct enumeration (`N ≤ N₀`); above it, a run is one fresh phase
(`fresh_phase_bound`). -/
theorem eq_main_recurrence (hP : P.Terminating) (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ)
    (hbase : AboveBase P cc) (hcσ : 0 ≤ cσ) (hw : NodeBound w cw af) (hcw : 0 ≤ cw)
    (haf : 0 ≤ af) (ha : af + 1 ≤ cc.a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, BddAbove (costSet w cσ N) ∧
      worstCost w cσ N ≤
        Real.exp (C * Real.log ((N : ℝ) + 2) ^ 2) * (1 + worstCost w cσ ⌈(N : ℝ) ^ P.γ⌉₊) := by
  obtain ⟨C₀, hC₀⟩ := main_phase_root_weight cc hcσ
  set C₁ := cw + 20 + max C₀ 0 + 3
  have hC₀' := le_max_right C₀ 0
  have hcwC : cw ≤ C₁ := by simp only [C₁]; linarith
  have hC₁ : 0 ≤ C₁ := hcw.trans hcwC
  have hγ0 : 0 ≤ P.γ := hc.γ_eq ▸ cc.γ_pos.le
  -- Every run on at most `n` positions costs at most `exp(C₁ (log(n+2))²)(1 + F(⌈n^γ⌉))`,
  -- once `F` is bounded below `n`.
  have elem : ∀ n : ℕ, (∀ m < n, BddAbove (costSet w cσ m)) → ∀ x ∈ costSet w cσ n,
      x ≤ expLogSq C₁ n * (1 + worstCost w cσ ⌈(n : ℝ) ^ P.γ⌉₊) := by
    intro n IH x ⟨Ω, C, S, L, A, r, hS, hok, hx⟩
    subst hx
    have hF0 := worstCost_nonneg hw.nonneg cσ ⌈(n : ℝ) ^ P.γ⌉₊
    have hE0 := expLogSq_nonneg C₁ n
    by_cases hs : S.size ≤ P.N₀
    · cases r with
      | direct _ hs' =>
        rw [Run.total_direct]
        have h1 := hw.solve (Run.direct (P := P) S hs').node rfl
        have h2 : expLogSq cw S.size ≤ expLogSq C₁ n :=
          (expLogSq_mono_right hcw hS).trans (expLogSq_mono_left hcwC n)
        have h3 : expLogSq C₁ n ≤ expLogSq C₁ n * (1 + worstCost w cσ ⌈(n : ℝ) ^ P.γ⌉₊) :=
          le_mul_of_one_le_right hE0 (by linarith)
        exact h1.trans (h2.trans h3)
      | fresh hs' => omega
    · push Not at hs
      obtain ⟨h6, h2, hlt⟩ := hbase S.size hs
      have hbs := IH _ (lt_of_lt_of_le hlt hS)
      have h := fresh_phase_bound hc hw hcw haf ha hαγ hP.third_lt_α hC₀ h6 h2 hbs r hs rfl hok
      have hn : P.N₀ < n := lt_of_lt_of_le hs hS
      have hbn := IH _ (hbase n hn).2.2
      have hceil : ⌈(S.size : ℝ) ^ P.γ⌉₊ ≤ ⌈(n : ℝ) ^ P.γ⌉₊ :=
        Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hS) hγ0)
      have hFm := worstCost_mono hw.nonneg hceil hbn
      have hE := expLogSq_mono_right hC₁ hS
      have hFs := worstCost_nonneg hw.nonneg cσ ⌈(S.size : ℝ) ^ P.γ⌉₊
      calc r.total w ≤ expLogSq C₁ S.size * (1 + worstCost w cσ ⌈(S.size : ℝ) ^ P.γ⌉₊) := h
        _ ≤ expLogSq C₁ n * (1 + worstCost w cσ ⌈(n : ℝ) ^ P.γ⌉₊) :=
          mul_le_mul hE (by linarith) (by linarith) hE0
  have hbdd : ∀ n : ℕ, BddAbove (costSet w cσ n) := fun n =>
    Nat.strong_induction_on n fun n IH => ⟨_, elem n IH⟩
  refine ⟨C₁, hC₁, fun N => ⟨hbdd N, ?_⟩⟩
  have hF0 := worstCost_nonneg hw.nonneg cσ ⌈(N : ℝ) ^ P.γ⌉₊
  exact Real.sSup_le (elem N fun m _ => hbdd m)
    (mul_nonneg (expLogSq_nonneg C₁ N) (by linarith))

/-- **The solution of eq. `main-recurrence`** (Section 7.4): the worst-case cost of a run
with root bounds on at most `N` positions is at most `exp(C' (log(N+2))²)`. -/
theorem main_recurrence_solved (hP : P.Terminating) (hc : Compat P cc) (hαγ : 2 * P.α ≤ P.γ)
    (hbase : AboveBase P cc) (hcσ : 0 ≤ cσ) (hw : NodeBound w cw af) (hcw : 0 ≤ cw)
    (haf : 0 ≤ af) (ha : af + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ N : ℕ, BddAbove (costSet w cσ N) ∧
      worstCost w cσ N ≤ Real.exp (C' * Real.log ((N : ℝ) + 2) ^ 2) := by
  obtain ⟨C, hC, h⟩ := eq_main_recurrence hP hc hαγ hbase hcσ hw hcw haf ha
  obtain ⟨C', hC'⟩ := main_recurrence_solution (hc.γ_eq ▸ cc.γ_pos) hP.γ_lt hC
    (worstCost w cσ) 0 (fun N _ => (h N).2)
  exact ⟨C', fun N => ⟨(h N).1, hC' N⟩⟩

end Recurrence

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2 at stage 1** (`thm:main-string`, String isomorphism). There is a constant
`C'` such that for every state `S` on a finite position set:

* `Solve` has a run on `S`;
* every run returns the exact transporter `{g ∈ G : y(g v) = x(v) for all v ∈ dom}`, which
  is empty or a coset `t · Aut_G(x)` (Lemma 6.1);
* every run with root bounds has total cost at most `exp(C' (log(s+2))²)`, where
  `s = |dom|`.

The hypotheses are the parameters of Sections 6 and 7.5, the existence data `Supply`
with Maróti's theorem, and the per-node hypothesis `NodeBound` on the work `w` with
`af + 1 ≤ a`. -/
theorem thm_main_string_stage1 (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (Su : Supply P) {cc : ChargingConstants} (hc : Compat P cc)
    (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc) {cσ : ℝ} (hcσ : 0 ≤ cσ)
    {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBound w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C),
      Nonempty (Run P .solve S none S.answer) ∧
      ∀ {A : Set (Perm Ω)} (r : Run P .solve S none A),
        (A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
          (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω)))) ∧
        (r.RootsOK cσ → r.total w ≤ Real.exp (C' * Real.log ((S.size : ℝ) + 2) ^ 2)) := by
  obtain ⟨C', h⟩ := main_recurrence_solved hP hc hαγ hbase hcσ hw hcw haf ha
  refine ⟨C', fun {Ω C} _ S => ⟨exists_run_solve hP hM ha128 Su S, fun {A} r => ⟨?_, ?_⟩⟩⟩
  · have hA : A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} := r.exact
    refine ⟨hA, ?_⟩
    rw [hA]
    exact answer_empty_or_coset S.dom_inv S.x S.y
  · intro hok
    exact (total_le_worstCost (h S.size).1 r le_rfl hok).trans (h S.size).2

/-! ### Theorem 1.1 -/

section Graph

variable {n : ℕ}

/-- The graph isomorphisms from `X` to `Y` are the coset `σ · Aut(X)` of any one of them. -/
theorem graph_isos_eq_coset (X Y : SimpleGraph (Fin n)) (σ : X ≃g Y) :
    {p : Perm (Fin n) | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} =
      (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n))) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, SetLike.mem_coe]
  constructor
  · intro hp
    refine ⟨(σ.toEquiv : Perm (Fin n))⁻¹ * p, ?_, by simp⟩
    intro u v
    have h1 := σ.map_adj_iff (v := σ.symm (p u)) (w := σ.symm (p v))
    simp only [RelIso.apply_symm_apply] at h1
    change X.Adj (σ.symm (p u)) (σ.symm (p v)) ↔ X.Adj u v
    rw [← h1, hp]
  · rintro ⟨a, ha, rfl⟩ u v
    change X.Adj u v ↔ Y.Adj (σ (a u)) (σ (a v))
    rw [σ.map_adj_iff]
    exact (ha u v).symm

/-- The pair state of Algorithm 1 has `n²` positions. -/
theorem graphState_size (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    [DecidableRel Y.Adj] : (graphState X Y).size = n * n := by
  simp [State.size, graphState]

/-- `log(n² + 2) ≤ 2 log(n + 2)`. -/
theorem log_sq_add_two_le (n : ℕ) :
    Real.log (((n * n : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← Real.log_rpow (by positivity)]
  apply Real.log_le_log (by positivity)
  push_cast
  rw [show ((n : ℝ) + 2) ^ (2 : ℝ) = ((n : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
  nlinarith

/-- **Theorem 1.1 at stage 1** (`thm:main-graph`, Graph isomorphism). There is a constant
`C'` such that for all graphs `X, Y` on `n` vertices, `Solve` has a run on the pair state
of Algorithm 1 (`GI.Paper.graphState`, `n²` positions), and every run `r` with answer
`A` satisfies:

* the vertex permutations induced by `A` are exactly the isomorphisms from `X` to `Y`;
* `A` is empty exactly when `X` and `Y` are not isomorphic;
* for every isomorphism `σ`, the induced permutations are the coset `σ · Aut(X)`: the
  answer is "one isomorphism and the full automorphism group of the first graph";
* if `r` has root bounds, its total cost is at most `exp(C' (log(n+2))²)`.

The hypotheses are those of `thm_main_string_stage1`. -/
theorem thm_main_graph_stage1 (hP : P.Terminating) (hM : GI.Cited.MarotiPrimitive)
    (ha128 : 128 ≤ P.a) (Su : Supply P) {cc : ChargingConstants} (hc : Compat P cc)
    (hαγ : 2 * P.α ≤ P.γ) (hbase : AboveBase P cc) {cσ : ℝ} (hcσ : 0 ≤ cσ)
    {w : Node P → ℝ} {cw af : ℝ} (hw : NodeBound w cw af) (hcw : 0 ≤ cw) (haf : 0 ≤ af)
    (ha : af + 1 ≤ cc.a) :
    ∃ C' : ℝ, ∀ (n : ℕ) (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj] [DecidableRel Y.Adj],
      Nonempty (Run P .solve (graphState X Y) none (graphState X Y).answer) ∧
      ∀ {A : Set (Perm (Fin n × Fin n))} (r : Run P .solve (graphState X Y) none A),
        diagonalHom (Fin n) ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
        (A = ∅ ↔ IsEmpty (X ≃g Y)) ∧
        (∀ σ : X ≃g Y, diagonalHom (Fin n) ⁻¹' A =
          (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n)))) ∧
        (r.RootsOK cσ → r.total w ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2)) := by
  obtain ⟨C', h⟩ := thm_main_string_stage1 hP hM ha128 Su hc hαγ hbase hcσ hw hcw haf ha
  refine ⟨4 * max C' 0, fun n X Y _ _ => ⟨(h (graphState X Y)).1, fun {A} r => ?_⟩⟩
  obtain ⟨hiso, hempty⟩ := alg_graph_wrapper X Y r
  refine ⟨hiso, hempty, fun σ => hiso.trans (graph_isos_eq_coset X Y σ), fun hok => ?_⟩
  have hcost := ((h (graphState X Y)).2 r).2 hok
  rw [graphState_size] at hcost
  refine hcost.trans (Real.exp_le_exp.mpr ?_)
  set L := Real.log ((n : ℝ) + 2)
  have hL0 : 0 ≤ Real.log (((n * n : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg (n * n) : (0 : ℝ) ≤ _); linarith)
  have hl := log_sq_add_two_le n
  have hsq : Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 ≤ 4 * L ^ 2 := by
    nlinarith
  have hm := le_max_left C' 0
  have hm0 := le_max_right C' 0
  have e1 : C' * Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 ≤
      max C' 0 * Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have e2 := mul_le_mul_of_nonneg_left hsq hm0
  push_cast at e1 e2 ⊢
  nlinarith

end Graph

end GI.Paper
