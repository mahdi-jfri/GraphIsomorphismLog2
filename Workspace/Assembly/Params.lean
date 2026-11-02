import Workspace.Paper.MainTheoremRoots
import Workspace.Paper.RunningTimeParameters
import Workspace.Paper.RunningTimeBaseSize
import Workspace.Algorithm.SupplyBuild
import Workspace.Algorithm.RowSupply

/-!
# The paper's parameters, fixed once

Sections 6 and 7 of the paper work with fixed constants. Section 7.5
("Choice of parameters") lists the conditions they must meet and gives example values:
`κ = 64`, `δ = 1/4`, `η = 3/4`, `β = 9/10`, `θ = 3/4`, `α = 2/5`, `γ = 9/10`. The other
constants are only asked to be "large enough":

* `q₀ ≥ 4κ + 2 = 258` (item (i)), and `q₀` "enlarged as needed for the coherent-configuration cap
  bounds" (item (i)): the explicit threshold of Lemma A.12 for `β ≥ 3/4` is
  `2(4·4⁴ + 8) = 2064` (`GI.Paper.a12Threshold`). We take `q₀ = 2064`; item (i) then gives
  `βq₀ ≥ 2`.
* `a ≥ 1` "large enough for all multiplicities and node tolls" (item (iv); Section 7.2). The
  recursion asks `a ≥ 128` (the enumeration exponent of Section A.5, `run_exists`) and
  `q₀! ≤ 2^⌊a log 2⌋` (`Params.EnumeratesBounded`: the bounded alternating degrees are
  enumerated; the paper fixes `q₀` in item (i) before `a` in item (iv); the exponent is the
  integer exponent of the small test `PrimitiveQuotient.SmallZ`). With `q₀ = 2064` the
  second condition needs `a ≥ 28503` or so (`log 2064! ≈ 13694`); the proof below uses
  `2064! ≤ 4096^2064 = 2^24768`, which needs `⌊a log 2⌋ ≥ 24768`, so `a ≥ 35733`. The charging
  argument asks `a + 1` for the constants ("after increasing this fixed `a`", Section 7.2). We
  take `a = 36000` in the recursion and `a = 36001` in the charging constants.
* `J = 8` (item (iv): "the six rows of the table … permit, for example, `J = 8`").
* `b₀` bounds the parity multiplicity of a row construction (item (iv)); we take `b₀ = 2`.
* `A, B, D` exist by item (iv) (`GI.Paper.sec_parameters_example_constants`); we pick them by
  choice, as the paper does ("choose one fixed `A`").
* `N₀` is the base size of the last paragraph of Section 7.5
  (`GI.Paper.sec_parameters_base_size_example`), at least 1.

`P₀` and `cc₀` are these values. `P₀_hyps` proves every parameter hypothesis of
`GI.Paper.thm_main_graph_stage1'` and `GI.Paper.run_exists` for them, and
`thm_main_graph_stage1''` is Theorem 1.1 at stage 1 at these parameters, for every run.
-/

namespace GI.Assembly

open GI.Algorithm GI.Paper Equiv Equiv.Perm
open scoped Pointwise

/-- The charging constants of Section 7.5 at the example values: `a = 36001`, `γ = 9/10`,
`κ = 64`, `θ = 3/4`, `β = 9/10`, `q₀ = 2064`, `J = 8`, `b₀ = 2`, and `A, B, D` as in item (iv). -/
noncomputable def cc₀ : ChargingConstants :=
  Classical.choose (sec_parameters_item_iv (a := 36001) (γ := 9 / 10) (κ := 64) (θ := 3 / 4)
    (β := 9 / 10) (q₀ := 2064) (J := 8) (b₀ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))

theorem cc₀_spec : cc₀.a = 36001 ∧ cc₀.γ = 9 / 10 ∧ cc₀.κ = 64 ∧ cc₀.θ = 3 / 4 ∧
    cc₀.β = 9 / 10 ∧ cc₀.q₀ = 2064 ∧ cc₀.J = 8 ∧ cc₀.b₀ = 2 :=
  Classical.choose_spec (sec_parameters_item_iv (a := 36001) (γ := 9 / 10) (κ := 64)
    (θ := 3 / 4) (β := 9 / 10) (q₀ := 2064) (J := 8) (b₀ := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))

/-- `36001 < (9/10) D`, from `D > a/γ + 2` (item (iv)). -/
theorem cc₀_D : (36001 : ℝ) < 9 / 10 * cc₀.D := by
  have h := cc₀.D_gt
  obtain ⟨ha, hγ, -⟩ := cc₀_spec
  rw [ha, hγ] at h
  linarith

/-- The base size of Section 7.5 for `α = 2/5`, `γ = 9/10`, `q₀ = 2064`, `a = 36001` and the
`D` of `cc₀`. -/
noncomputable def baseN₀ : ℕ :=
  Classical.choose (sec_parameters_base_size_example 2064 36001 cc₀.D cc₀_D)

theorem baseN₀_spec : ∀ N : ℕ, baseN₀ ≤ N →
      (N : ℝ) < ((⌊(N : ℝ) ^ (2 / 5 : ℝ)⌋₊).choose 3 : ℝ) ∧
      (N : ℝ) ^ (1 - 2 / 5 : ℝ) < ((⌊(N : ℝ) ^ (2 / 5 : ℝ)⌋₊).choose 2 : ℝ) ∧
      (2064 : ℝ) < (N : ℝ) ^ (2 / 5 : ℝ) ∧
      (∃ k : ℕ, Odd k ∧ 8 < k ∧ 2 + Real.logb 2 N < k ∧
        (2 * k - 1 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ)) ∧
      6 ≤ (N : ℝ) ^ (9 / 10 : ℝ) ∧ ⌈(N : ℝ) ^ (9 / 10 : ℝ)⌉₊ < N ∧
      2 ≤ (N : ℝ) ^ (9 / 10 * cc₀.D - 36001 : ℝ) := by
  exact Classical.choose_spec (sec_parameters_base_size_example 2064 36001 cc₀.D cc₀_D)

/-- **The parameters of the paper** (Section 7.5), as one `Params` value. -/
noncomputable def P₀ : Params where
  α := 2 / 5
  γ := 9 / 10
  N₀ := max baseN₀ 1
  κ := 64
  a := 36000
  θ := 3 / 4
  β := 9 / 10
  q₀ := 2064
  b₀ := 2

/-- The parameter inequalities of Section 6 (`Params.Terminating`) hold for `P₀`. -/
theorem P₀_terminating : P₀.Terminating where
  N₀_pos := le_max_right _ _
  γ_lt := by norm_num [P₀]
  α_pos := by norm_num [P₀]
  third_lt_α := by norm_num [P₀]
  two_α_lt := by norm_num [P₀]
  θ_lt := by norm_num [P₀]
  κ_five := by norm_num [P₀]
  β_lt := by norm_num [P₀]
  q₀_pos := by norm_num [P₀]

theorem P₀_a : 128 ≤ P₀.a := by norm_num [P₀]

theorem P₀_γ : 0 ≤ P₀.γ := by norm_num [P₀]

/-- **The bounded alternating degrees are enumerated**: `2064! ≤ 2^⌊36000 log 2⌋`. Indeed
`2064! ≤ 2064^2064 ≤ 4096^2064 = 2^24768`, and `24768 ≤ ⌊36000 log 2⌋` since `log 2 > 0.69`. -/
theorem P₀_enumeratesBounded : P₀.EnumeratesBounded := by
  unfold Params.EnumeratesBounded
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hb : 24768 ≤ P₀.smallExp := by
    unfold Params.smallExp
    apply Nat.le_floor
    show ((24768 : ℕ) : ℝ) ≤ (36000 : ℝ) * Real.log 2
    push_cast
    linarith
  have h1 : Nat.factorial 2064 ≤ 2 ^ 24768 := by
    have := Nat.factorial_le_pow 2064
    have h2 : (2064 : ℕ) ^ 2064 ≤ 4096 ^ 2064 := Nat.pow_le_pow_left (by norm_num) _
    have h3 : (4096 : ℕ) ^ 2064 = 2 ^ 24768 := by
      rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, ← pow_mul]
    exact this.trans (h2.trans h3.le)
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) hb)

/-- The exponent of the integer small test at `P₀`: `⌊36000 log 2⌋ = 24953`, since
`0.6931471803 < log 2 < 0.6931471808`. -/
theorem P₀_smallExp : P₀.smallExp = 24953 := by
  unfold Params.smallExp
  rw [Nat.floor_eq_iff (by have := Real.log_two_gt_d9; show (0 : ℝ) ≤ 36000 * Real.log 2; positivity)]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  show ((24953 : ℕ) : ℝ) ≤ 36000 * Real.log 2 ∧ 36000 * Real.log 2 < ((24953 : ℕ) : ℝ) + 1
  push_cast
  constructor <;> linarith

theorem P₀_κ : 64 ≤ P₀.κ := by norm_num [P₀]

theorem P₀_αγ : 2 * P₀.α ≤ P₀.γ := by norm_num [P₀]

/-- The recursion and the charging constants agree (`Compat`). -/
theorem P₀_compat : Compat P₀ cc₀ := by
  obtain ⟨ha, hγ, hκ, hθ, hβ, hq, hJ, -⟩ := cc₀_spec
  exact
    { γ_eq := by rw [hγ]; rfl
      a_le := by rw [ha]; norm_num [P₀]
      θ_le := by rw [hθ]; norm_num [P₀]
      κ_le := by rw [hκ]; norm_num [P₀]
      κ_five := by norm_num [P₀]
      β_pos := by norm_num [P₀]
      β_le := by rw [hβ]; norm_num [P₀]
      q₀_le := by rw [hq]; norm_num [P₀]
      βq₀ := by norm_num [P₀]
      J_six := by rw [hJ]; norm_num }

/-- `N₀` is above the base size (`AboveBase`). -/
theorem P₀_aboveBase : AboveBase P₀ cc₀ := by
  intro n hn
  have hn' : baseN₀ ≤ n := (le_max_left _ _).trans (le_of_lt (by simpa [P₀] using hn))
  obtain ⟨-, -, -, -, h6, hceil, h2⟩ := baseN₀_spec n hn'
  obtain ⟨ha, hγ, -⟩ := cc₀_spec
  refine ⟨by rw [hγ]; exact h6, by rw [hγ, ha]; exact h2, ?_⟩
  simpa [P₀] using hceil

/-- `a + 1 ≤ a` of the charging constants (Section 7.2: "after increasing this fixed `a`"). -/
theorem P₀_a_succ : P₀.a + 1 ≤ cc₀.a := by
  rw [cc₀_spec.1]; norm_num [P₀]

/-- **The row threshold holds at `P₀`**. It follows from the third base-size condition
`2064 < N^{2/5}` of Section 7.5 (`baseN₀_spec`): put `t = N^{2/5}` and `u = √t > 16`. Then
`log₂ N = (5/2) log t / log 2 ≤ 5 u / log 2`, since `log t ≤ 2√t`, and
`2 (2 + log₂ N) + 3 ≤ 7 + 10 u / log 2 ≤ 7 + 15 u ≤ u² = t`. -/
theorem P₀_rowThreshold : P₀.RowThreshold := by
  intro N hN
  have hN' : baseN₀ ≤ N := (le_max_left _ _).trans (le_of_lt (by simpa [P₀] using hN))
  have hN1 : 1 ≤ N := (le_max_right baseN₀ 1).trans (le_of_lt (by simpa [P₀] using hN))
  obtain ⟨-, -, h258, -⟩ := baseN₀_spec N hN'
  have hα : P₀.α = 2 / 5 := rfl
  rw [hα]
  set t : ℝ := (N : ℝ) ^ (2 / 5 : ℝ) with ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have ht0 : 0 < t := Real.rpow_pos_of_pos hNpos _
  -- `log t = (2/5) log N`.
  have hlogt : Real.log t = 2 / 5 * Real.log N := Real.log_rpow hNpos _
  -- `log t ≤ 2 √t`.
  have hlog_le : Real.log t ≤ 2 * Real.sqrt t := by
    have := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  set u := Real.sqrt t with hu
  have hu2 : u ^ 2 = t := Real.sq_sqrt ht0.le
  have hu16 : 16 < u := by
    rw [hu, show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogb : Real.logb 2 N = 5 / 2 * Real.log t / Real.log 2 := by
    rw [Real.logb, hlogt]; ring
  have hb : Real.logb 2 N ≤ 5 * u / Real.log 2 := by
    rw [hlogb, div_le_div_iff_of_pos_right (by linarith)]
    linarith
  have hb' : Real.logb 2 N ≤ 15 / 2 * u := by
    refine hb.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rcases le_total 8 (2 + Real.logb 2 N) with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

/-- **Every parameter hypothesis** of `GI.Paper.thm_main_graph_stage1'`, `GI.Paper.run_exists`,
`GI.Paper.run_exists_giant`, `GI.Paper.thm_main_graph_stage1_giant` and (with `RowThreshold`)
`GI.Paper.thm_main_graph_stage1_carrier` holds for `P₀` and `cc₀`. -/
theorem P₀_hyps : P₀.Terminating ∧ 128 ≤ P₀.a ∧ 64 ≤ P₀.κ ∧ Compat P₀ cc₀ ∧
    2 * P₀.α ≤ P₀.γ ∧ AboveBase P₀ cc₀ ∧ P₀.a + 1 ≤ cc₀.a ∧ 0 ≤ P₀.γ ∧
    P₀.EnumeratesBounded ∧ P₀.RowThreshold :=
  ⟨P₀_terminating, P₀_a, P₀_κ, P₀_compat, P₀_αγ, P₀_aboveBase, P₀_a_succ, P₀_γ,
    P₀_enumeratesBounded, P₀_rowThreshold⟩

/-- **Theorem 1.1 at stage 1, at the paper's parameters, for every run.** Assume the cited
results `AutCardLeSq` and `SimpleValuationDegree` (the inputs of Theorem A.9), and the work
bounds `NodeBound' w cw` with `0 ≤ cw`. Then there is a constant `C'` such that for all graphs
`X, Y` on `n` vertices, every run `r` of `Solve` on the pair state of Algorithm 1 with answer `A`
gives exactly the isomorphisms from `X` to `Y` (empty exactly when there is none, and
`σ · Aut(X)` for every isomorphism `σ`), and has total cost at most `exp(C' (log(n+2))²)`.

Compared with `GI.Paper.thm_main_graph_stage1'`: the parameters are fixed to `P₀`, and the
existence of a run is left out, so neither `Supply` nor Maróti's theorem is needed. -/
theorem thm_main_graph_stage1'' (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) {w : Node P₀ → ℝ} {cw : ℝ} (hw : NodeBound' w cw)
    (hcw : 0 ≤ cw) :
    ∃ C' : ℝ, ∀ (n : ℕ) (X Y : SimpleGraph (Fin n)) [DecidableRel X.Adj] [DecidableRel Y.Adj]
      {A : Set (Perm (Fin n × Fin n))} (r : Run P₀ .solve (graphState X Y) none A),
        diagonalHom (Fin n) ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
        (A = ∅ ↔ IsEmpty (X ≃g Y)) ∧
        (∀ σ : X ≃g Y, diagonalHom (Fin n) ⁻¹' A =
          (σ.toEquiv : Perm (Fin n)) • (GI.Statement.autGroup X : Set (Perm (Fin n)))) ∧
        r.total w ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) := by
  obtain ⟨hP, ha128, hκ, hc, hαγ, hbase, ha, -⟩ := P₀_hyps
  obtain ⟨cσ, hcσ, hok⟩ := Run.rootsOK_all hAut hLie hκ
  have h5 : (5 : ℝ) ≤ P₀.a := by linarith
  obtain ⟨C', h⟩ := main_recurrence_solved hP hc hαγ hbase hcσ (hw.toNodeBound h5) hcw
    (by linarith) ha
  refine ⟨4 * max C' 0, fun n X Y _ _ A r => ?_⟩
  obtain ⟨hiso, hempty⟩ := alg_graph_wrapper X Y r
  refine ⟨hiso, hempty, fun σ => hiso.trans (graph_isos_eq_coset X Y σ), ?_⟩
  have hcost := (total_le_worstCost (h (graphState X Y).size).1 r le_rfl (hok r)).trans
    (h (graphState X Y).size).2
  rw [graphState_size] at hcost
  refine hcost.trans (Real.exp_le_exp.mpr ?_)
  set L := Real.log ((n : ℝ) + 2)
  have hl := log_sq_add_two_le n
  have hL0 : 0 ≤ Real.log (((n * n : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg (n * n) : (0 : ℝ) ≤ _); linarith)
  have hsq : Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hm := le_max_left C' 0
  have hm0 := le_max_right C' 0
  have e1 : C' * Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 ≤
      max C' 0 * Real.log (((n * n : ℕ) : ℝ) + 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have e2 := mul_le_mul_of_nonneg_left hsq hm0
  push_cast at e1 e2 ⊢
  nlinarith

end GI.Assembly
