module

public import Workspace.Assembly.Params
public import Workspace.Algorithm.AggregationParams

@[expose] public section

/-!
# The parameter conditions of an aggregation round at `P₀`

`P₀_aggregates` proves `Params.Aggregates P₀` (`Workspace/Algorithm/AggregationParams.lean`) from
Corollary A.25. The inequalities
are the example values of Section 7.5. The support classification above the base size comes from
the base-size conditions of Section 7.5 (`baseN₀_spec`): for `N ≥ N₀` and `q > N^{2/5}`,

* `q > N^{2/5} > q₀ = 2064 ≥ 201`, the threshold of Lemma A.24;
* `s ≤ N < C(⌊N^{2/5}⌋, 3) ≤ C(q, 3)`;
* the odd `k > max{63, 12 log₂ N}` with `2k - 1 ≤ N^{2/5} < q` gives
  `max{63, 12 log₂ s} < k < q`.

These are the hypotheses of Corollary A.25 (`GI.Paper.cor_physical_support_thresholds`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Paper

/-- **The support classification above the base size at `P₀`** (Section 6.2, "Why the cases
cover every large action", with the base size of Section 7.5). -/
theorem P₀_supportCases :
    ∀ N : ℕ, P₀.N₀ < N → SupportCases P₀.α N := by
  intro N hN Ω Γ _ _ _ _ G _ φ hφ hΩ hΓ
  have hN' : baseN₀ ≤ N := (le_max_left _ _).trans (le_of_lt (by simpa [P₀] using hN))
  have hN1 : 1 ≤ N := (le_max_right baseN₀ 1).trans (le_of_lt (by simpa [P₀] using hN))
  obtain ⟨h3, -, hq₀, ⟨k, -, hk63, hklog, hk⟩, -⟩ := baseN₀_spec N hN'
  have hα : P₀.α = 2 / 5 := rfl
  rw [hα] at hΓ
  set q := Fintype.card Γ
  set x := (N : ℝ) ^ (2 / 5 : ℝ)
  -- `q ≥ 201`
  have hm : GI.SupportThresholds.lowIndexThreshold ≤ q := by
    have : (2064 : ℝ) < q := hq₀.trans hΓ
    have : 2064 < q := by exact_mod_cast this
    show 201 ≤ q
    omega
  -- `s ≤ N < C(⌊N^{2/5}⌋, 3) ≤ C(q, 3)`
  have hn : Fintype.card Ω < q.choose 3 := by
    have hfl : ⌊x⌋₊ ≤ q := Nat.floor_le_of_le hΓ.le
    have h1 : N < (⌊x⌋₊).choose 3 := by exact_mod_cast h3
    exact lt_of_le_of_lt hΩ (lt_of_lt_of_le h1 (Nat.choose_le_choose 3 hfl))
  -- `max{63, 12 log₂ s} < k < q`
  have hlog : max 63 (12 * Real.logb 2 (Fintype.card Ω)) < (q : ℝ) := by
    have hkq : (k : ℝ) < q := by
      have : (k : ℝ) ≤ 2 * k - 1 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        linarith
      linarith
    have hk63' : (63 : ℝ) < k := by exact_mod_cast hk63
    have hls : Real.logb 2 (Fintype.card Ω) ≤ Real.logb 2 N := by
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]
        exact Real.logb_nonneg one_lt_two hN1'
      · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h0) (by exact_mod_cast hΩ)
    exact max_lt (by linarith) (by linarith)
  exact (cor_physical_support_thresholds G φ hφ hm hn hlog).1

/-- **The parameter conditions of an aggregation round hold at `P₀`.** -/
theorem P₀_aggregates : P₀.Aggregates where
  β_cfg := by norm_num [P₀]
  θ_half := by norm_num [P₀]
  θκ := by norm_num [P₀]
  κ_five := by norm_num [P₀]
  κ_seven := by norm_num [P₀]
  q₀_cert := by norm_num [P₀]
  q₀_cfg := by norm_num [P₀, GI.Paper.a12Threshold]
  a_cert := by norm_num [P₀]
  cases := P₀_supportCases

end GI.Assembly
