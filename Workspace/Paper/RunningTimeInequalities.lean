import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorial.Basic
import Workspace.TowerRank

/-!
# Section 7: the displayed inequalities

The scalar inequalities of Section 7.1 to 7.3 of the paper
("Running time"), one declaration per displayed formula. Each is proved for all
values in the range the paper states. Lemma 7.1 itself is in
`Workspace/Paper/RunningTime.lean`.
-/

namespace GI.Paper

open Real Finset

/-! ## Equation (main-rho) and (main-Q) -/

/-- Equation `eq:main-rho`: for interval ratios `d i ≥ 1` with product `s`,
`ρ = Σ (2⌊log₂ d_i⌋ - 1)` over the nontrivial ratios is at most `2 log₂ s`.
`towerRank` gives `0` on a trivial ratio, so the sum may run over all intervals. -/
theorem eq_main_rho {ι : Type*} (I : Finset ι) (d : ι → ℕ) (hd : ∀ i ∈ I, 1 ≤ d i) :
    ((∑ i ∈ I, GI.towerRank (d i) : ℤ) : ℝ) ≤ 2 * Real.logb 2 ((∏ i ∈ I, d i : ℕ) : ℝ) := by
  classical
  have hterm : ∀ i ∈ I, ((GI.towerRank (d i) : ℤ) : ℝ) ≤ 2 * Real.logb 2 (d i : ℝ) := by
    intro i hi
    unfold GI.towerRank
    split_ifs with h
    · have : (1 : ℝ) ≤ d i := by exact_mod_cast hd i hi
      have := Real.logb_nonneg (b := 2) (by norm_num) this
      simp; linarith
    · have hl := Real.natLog_le_logb (d i) 2
      push_cast
      push_cast at hl
      linarith
  have hprod : Real.logb 2 ((∏ i ∈ I, d i : ℕ) : ℝ) = ∑ i ∈ I, Real.logb 2 (d i : ℝ) := by
    push_cast
    rw [Real.logb_prod]
    intro i hi
    have : (1 : ℝ) ≤ d i := by exact_mod_cast hd i hi
    positivity
  rw [hprod, mul_sum]
  push_cast
  exact sum_le_sum hterm

/-- Equation `eq:main-Q`: if every stored bound satisfies `c_i ≤ d_i` (Section 3.2:
"every stored bound is at most its current interval ratio") and the ratios have
product `s`, then `Q = Σ (log d_i) log max{c_i,2} ≤ (log s)²`. -/
theorem eq_main_Q {ι : Type*} (I : Finset ι) (d c : ι → ℕ) (hd : ∀ i ∈ I, 1 ≤ d i)
    (hc : ∀ i ∈ I, c i ≤ d i) :
    ∑ i ∈ I, Real.log (d i : ℝ) * Real.log (max (c i : ℝ) 2) ≤
      (Real.log ((∏ i ∈ I, d i : ℕ) : ℝ)) ^ 2 := by
  have hlog0 : ∀ i ∈ I, 0 ≤ Real.log (d i : ℝ) := fun i hi =>
    Real.log_nonneg (by exact_mod_cast hd i hi)
  have hterm : ∀ i ∈ I, Real.log (d i : ℝ) * Real.log (max (c i : ℝ) 2) ≤
      Real.log (d i : ℝ) * Real.log (d i : ℝ) := by
    intro i hi
    by_cases h1 : d i = 1
    · simp [h1]
    · have h2 : (2 : ℝ) ≤ d i := by
        have := hd i hi; exact_mod_cast (by omega : 2 ≤ d i)
      apply mul_le_mul_of_nonneg_left _ (hlog0 i hi)
      apply Real.log_le_log (by positivity)
      exact max_le (by exact_mod_cast hc i hi) h2
  have hprod : Real.log ((∏ i ∈ I, d i : ℕ) : ℝ) = ∑ i ∈ I, Real.log (d i : ℝ) := by
    push_cast
    rw [Real.log_prod]
    intro i hi
    have : (1 : ℝ) ≤ d i := by exact_mod_cast hd i hi
    positivity
  rw [hprod]
  calc _ ≤ ∑ i ∈ I, Real.log (d i : ℝ) * Real.log (d i : ℝ) := sum_le_sum hterm
    _ ≤ ∑ i ∈ I, Real.log (d i : ℝ) * ∑ j ∈ I, Real.log (d j : ℝ) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (single_le_sum hlog0 hi) (hlog0 i hi)
    _ = _ := by rw [← sum_mul, pow_two]

/-! ## Equation (main-phase-active) -/

/-- Equation `eq:main-phase-active`: if `s > N^γ` then `N^a ≤ exp(a_* x)` with
`a_* = a/γ` and `x = log(s+2)`. -/
theorem eq_main_phase_active {N s a γ : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) (hγ : 0 < γ)
    (hs : N ^ γ < s) : N ^ a ≤ Real.exp (a / γ * Real.log (s + 2)) := by
  rcases hN.eq_or_lt with h0 | hN
  · subst h0
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0; simp
    · rw [Real.zero_rpow ha0.ne']; positivity
  · have hNγ : 0 < N ^ γ := Real.rpow_pos_of_pos hN γ
    have hlog : γ * Real.log N < Real.log (s + 2) := by
      rw [← Real.log_rpow hN]
      exact Real.log_lt_log hNγ (by linarith)
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.mpr
    have : Real.log N * a ≤ a / γ * (γ * Real.log N) := by
      field_simp; linarith
    have h2 : a / γ * (γ * Real.log N) ≤ a / γ * Real.log (s + 2) :=
      mul_le_mul_of_nonneg_left hlog.le (div_nonneg ha hγ.le)
    linarith

/-! ## Equation (main-domain-payment) -/

/-- The first claim before `eq:main-domain-payment`: for `θ > 1/2` and `s ≥ 6`,
`s ≥ 2/√θ`. -/
theorem main_domain_payment_size {θ s : ℝ} (hθ : 1 / 2 < θ) (hs : 6 ≤ s) :
    2 / Real.sqrt θ ≤ s := by
  have hθ0 : 0 < θ := by linarith
  have hsq : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ0
  rw [div_le_iff₀ hsq]
  have h1 : (1 / 2 : ℝ) ≤ Real.sqrt θ := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

/-- Equation `eq:main-domain-payment`, for `1/2 < θ < 1` and `s ≥ 6`, with
`c_θ = (1/2) log(1/θ)` and `x = log(s+2)`. -/
theorem eq_main_domain_payment {θ s : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ < 1) (hs : 6 ≤ s) :
    (1 / 2) * Real.log (1 / θ) ≤ Real.log (s + 2) - Real.log (θ * s + 2) ∧
    (1 / 2) * Real.log (1 / θ) * Real.log (s + 2) ≤
      Real.log (s + 2) ^ 2 - Real.log (θ * s + 2) ^ 2 := by
  have hθ0 : 0 < θ := by linarith
  have hy : 0 < θ * s + 2 := by positivity
  -- `θ(s+2)² ≥ (θs+2)²`, because the difference is `(1-θ)(θs²-4)`.
  have hsq : (θ * s + 2) ^ 2 ≤ θ * (s + 2) ^ 2 := by
    have h4 : 0 ≤ θ * s ^ 2 - 4 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) h4]
  have h1 : (1 / 2) * Real.log (1 / θ) ≤ Real.log (s + 2) - Real.log (θ * s + 2) := by
    have := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow, Real.log_mul hθ0.ne' (by positivity), Real.log_pow] at this
    simp only [one_div, Real.log_inv]
    push_cast at this
    linarith
  refine ⟨h1, ?_⟩
  have hx0 : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ Real.log (θ * s + 2) := Real.log_nonneg (by nlinarith)
  have hc0 : 0 ≤ (1 / 2) * Real.log (1 / θ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by rw [le_div_iff₀ hθ0]; linarith))
  nlinarith [mul_le_mul h1 (le_add_of_nonneg_right hy0 : Real.log (s + 2) ≤
    Real.log (s + 2) + Real.log (θ * s + 2)) hx0 (by linarith)]

/-! ## Equation (main-enumeration-payment) -/

/-- Equation `eq:main-enumeration-payment`, uniformly for `s ≥ d ≥ 2`. -/
theorem eq_main_enumeration_payment {s d : ℝ} (hd : 2 ≤ d) (hsd : d ≤ s) :
    (d + 2) / 3 ≤ (s + 2) / (s / d + 2) ∧ d ^ (1 / 3 : ℝ) ≤ (d + 2) / 3 ∧
    (1 / 3) * Real.log (s + 2) * Real.log d ≤
      Real.log (s + 2) ^ 2 - Real.log (s / d + 2) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s := by linarith
  have hy : 0 < s / d + 2 := by positivity
  -- The ratio: `3d(s+2) - (d+2)(s+2d) = 2(d-1)(s-d) ≥ 0`.
  have hratio : (d + 2) / 3 ≤ (s + 2) / (s / d + 2) := by
    rw [div_le_div_iff₀ (by norm_num) hy]
    have : (d + 2) * (s / d + 2) * d = (d + 2) * (s + 2 * d) := by field_simp
    have h3 : (d + 2) * (s + 2 * d) ≤ (s + 2) * 3 * d := by nlinarith
    nlinarith
  -- Arithmetic–geometric mean: `(d+2)³ - 27d = (d-1)²(d+8) ≥ 0`.
  have hcube : d ≤ ((d + 2) / 3) ^ 3 := by nlinarith [sq_nonneg (d - 1)]
  have hamgm : d ^ (1 / 3 : ℝ) ≤ (d + 2) / 3 := by
    calc d ^ (1 / 3 : ℝ) ≤ (((d + 2) / 3) ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hd0.le hcube (by norm_num)
      _ = (d + 2) / 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  refine ⟨hratio, hamgm, ?_⟩
  -- Hence `x - log(s/d+2) ≥ (1/3) log d`.
  have hdiff : (1 / 3) * Real.log d ≤ Real.log (s + 2) - Real.log (s / d + 2) := by
    have h1 : Real.log (d ^ (1 / 3 : ℝ)) ≤ Real.log ((s + 2) / (s / d + 2)) :=
      Real.log_le_log (by positivity) (hamgm.trans hratio)
    rw [Real.log_rpow hd0, Real.log_div (by positivity) hy.ne'] at h1
    linarith
  have hx0 : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ Real.log (s / d + 2) := Real.log_nonneg (by linarith [div_nonneg hs0.le hd0.le])
  have hl0 : 0 ≤ (1 / 3) * Real.log d := mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  nlinarith [mul_le_mul hdiff (le_add_of_nonneg_right hy0 : Real.log (s + 2) ≤
    Real.log (s + 2) + Real.log (s / d + 2)) hx0 (by linarith)]

/-! ## The product-refinement bound -/

/-- The display after "Since `r ≤ log₂ s`" in Section 7.2: for a product exponent
`r ≥ 2` on `s` positions with `r ≤ log₂ s`, `log(2^r r!) ≤ r log(2r) ≤ 4(r-1)x`. -/
theorem main_product_index_bound {r s : ℕ} (hr : 2 ≤ r)
    (hrs : (r : ℝ) ≤ Real.logb 2 s) :
    Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ)) ≤ r * Real.log (2 * r) ∧
    (r : ℝ) * Real.log (2 * r) ≤ 4 * ((r : ℝ) - 1) * Real.log (s + 2) := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  constructor
  · -- `r! ≤ r^r`, so `2^r r! ≤ (2r)^r`.
    have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    have : (2 : ℝ) ^ r * (r.factorial : ℝ) ≤ (2 * r) ^ r := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hf (by positivity)
    calc Real.log ((2 : ℝ) ^ r * (r.factorial : ℝ)) ≤ Real.log ((2 * r) ^ r) :=
          Real.log_le_log (by positivity) this
      _ = r * Real.log (2 * r) := by rw [Real.log_pow]
  · -- `r ≤ log₂ s` gives `r < 2^r ≤ s`, hence `2r ≤ (s+2)²`.
    have hspos : (0 : ℝ) < s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h; simp at hrs; linarith
      · exact_mod_cast h
    rw [Real.le_logb_iff_rpow_le (by norm_num) hspos, Real.rpow_natCast] at hrs
    have hlt : (r : ℝ) < 2 ^ r := by exact_mod_cast Nat.lt_two_pow_self
    have hx : Real.log (2 * r) ≤ 2 * Real.log (s + 2) := by
      rw [← Real.log_rpow (by linarith), Real.rpow_two]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hx0 : 0 ≤ Real.log (2 * (r : ℝ)) := Real.log_nonneg (by linarith)
    nlinarith

/-! ## Equation (main-orbit-slack) -/

/-- `x^n - y^n = (x-y) Σ_{i<n} x^i y^(n-1-i)`, and the sum grows with `x` and `y`. So
`(w+c)^n - w^n` grows with `w ≥ 0` when `c ≥ 0`. This is the convexity used in
Section 7.3. -/
theorem pow_shift_sub_mono {w w' c : ℝ} (hw : 0 ≤ w) (hww : w ≤ w') (hc : 0 ≤ c) (n : ℕ) :
    (w + c) ^ n - w ^ n ≤ (w' + c) ^ n - w' ^ n := by
  rw [← geom_sum₂_mul, ← geom_sum₂_mul]
  simp only [add_sub_cancel_left]
  apply mul_le_mul_of_nonneg_right _ hc
  apply sum_le_sum
  intro i _
  apply mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) _)
    (pow_le_pow_left₀ hw hww _) (pow_nonneg hw _) (pow_nonneg (by linarith) _)

/-- Merging two orbits of sizes `a,b ≥ 1` into sizes `a+b-1` and `1` does not
decrease `Σ (s_i+2)^D`: with `u = a+2, v = b+2 ≥ 3`,
`u^n + v^n ≤ (u+v-3)^n + 3^n`. -/
theorem pow_merge {u v : ℝ} (hu : 3 ≤ u) (hv : 3 ≤ v) (n : ℕ) :
    u ^ n + v ^ n ≤ (u + v - 3) ^ n + 3 ^ n := by
  have := pow_shift_sub_mono (w := 3) (w' := u) (c := v - 3) (by norm_num) hu (by linarith) n
  have e1 : (3 : ℝ) + (v - 3) = v := by ring
  have e2 : u + (v - 3) = u + v - 3 := by ring
  rw [e1, e2] at this
  linarith

/-- `2·3^D ≤ 4^D` for `D ≥ 3`. -/
theorem two_mul_three_pow_le {D : ℕ} (hD : 3 ≤ D) : 2 * (3 : ℝ) ^ D ≤ 4 ^ D := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hD
  rw [pow_add, pow_add]
  have : (3 : ℝ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
  norm_num
  nlinarith

/-- The sum of prefactors over disjoint nonempty orbits. For a nonempty family of
sizes `t_i ≥ 1` with total `S`, `Σ (t_i+2)^D ≤ (S+2)^D`; with at least two members,
`Σ (t_i+2)^D ≤ (S+1)^D + 3^D`. -/
theorem prefactor_sum_aux {ι : Type*} [DecidableEq ι] {D : ℕ} (hD : 3 ≤ D)
    (t : ι → ℝ) (I : Finset ι) (ht : ∀ i ∈ I, 1 ≤ t i) :
    (I.Nonempty → ∑ i ∈ I, (t i + 2) ^ D ≤ (∑ i ∈ I, t i + 2) ^ D) ∧
    (2 ≤ I.card → ∑ i ∈ I, (t i + 2) ^ D ≤ (∑ i ∈ I, t i + 1) ^ D + 3 ^ D) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    have ht' : ∀ i ∈ I, 1 ≤ t i := fun i hi => ht i (mem_insert_of_mem hi)
    have hta : 1 ≤ t a := ht a (mem_insert_self a I)
    obtain ⟨_, _⟩ := ih ht'
    rw [sum_insert ha, sum_insert ha, card_insert_of_notMem ha]
    rcases I.eq_empty_or_nonempty with hI | hI
    · subst hI; simp
    · have hR : 1 ≤ ∑ i ∈ I, t i := by
        obtain ⟨j, hj⟩ := hI
        calc (1 : ℝ) ≤ t j := ht' j hj
          _ ≤ ∑ i ∈ I, t i := single_le_sum (fun i hi => by linarith [ht' i hi]) hj
      have hIH : ∑ i ∈ I, (t i + 2) ^ D ≤ (∑ i ∈ I, t i + 2) ^ D := by
        rename_i h1 _; exact h1 hI
      have hmerge := pow_merge (u := t a + 2) (v := ∑ i ∈ I, t i + 2) (by linarith)
        (by linarith) D
      have htwo : (t a + 2) ^ D + ∑ i ∈ I, (t i + 2) ^ D ≤
          (t a + ∑ i ∈ I, t i + 1) ^ D + 3 ^ D := by
        have e : t a + 2 + (∑ i ∈ I, t i + 2) - 3 = t a + ∑ i ∈ I, t i + 1 := by ring
        rw [e] at hmerge; linarith
      refine ⟨fun _ => ?_, fun _ => htwo⟩
      -- `(S+1)^D + 3^D ≤ (S+2)^D` for `S ≥ 2`, since `4^D - 3^D ≥ 3^D`.
      have hmono := pow_shift_sub_mono (w := 3) (w' := t a + ∑ i ∈ I, t i + 1) (c := 1)
        (by norm_num) (by linarith) (by norm_num) D
      have h43 := two_mul_three_pow_le hD
      norm_num at hmono
      have e : t a + ∑ i ∈ I, t i + 1 + 1 = t a + ∑ i ∈ I, t i + 2 := by ring
      rw [e] at hmono
      linarith

/-- The prefactors of disjoint nonempty orbits inside a domain of size `s` sum to at
most `(s+2)^D` (used in the proof of Lemma 7.1: "Within one branch, the prefactors of
its disjoint orbit children sum to at most `(s+2)^D`"). -/
theorem prefactor_sum_le {ι : Type*} {D : ℕ} (hD : 3 ≤ D) (t : ι → ℝ) (I : Finset ι)
    (ht : ∀ i ∈ I, 1 ≤ t i) {s : ℝ} (hs : ∑ i ∈ I, t i ≤ s) :
    ∑ i ∈ I, (t i + 2) ^ D ≤ (s + 2) ^ D := by
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI; simp only [sum_empty]
    have : (0 : ℝ) ≤ s := by simpa using hs
    positivity
  · have hS : 0 ≤ ∑ i ∈ I, t i := sum_nonneg fun i hi => by linarith [ht i hi]
    calc _ ≤ (∑ i ∈ I, t i + 2) ^ D := (prefactor_sum_aux hD t I ht).1 hI
      _ ≤ (s + 2) ^ D := pow_le_pow_left₀ (by linarith) (by linarith) D

/-- Equation `eq:main-orbit-slack`, first inequality: for `t ≥ 2` disjoint nonempty
orbits with total size at most `s` and an integer `D ≥ 3`,
`Σ (s_i+2)^D ≤ (s+1)^D + 3^D`. The sizes may be any reals `≥ 1`. -/
theorem eq_main_orbit_slack_sum {ι : Type*} {D : ℕ} (hD : 3 ≤ D) (t : ι → ℝ)
    (I : Finset ι) (ht : ∀ i ∈ I, 1 ≤ t i) (hcard : 2 ≤ I.card) {s : ℝ}
    (hs : ∑ i ∈ I, t i ≤ s) :
    ∑ i ∈ I, (t i + 2) ^ D ≤ (s + 1) ^ D + 3 ^ D := by
  classical
  have hS : 0 ≤ ∑ i ∈ I, t i := sum_nonneg fun i hi => by linarith [ht i hi]
  calc _ ≤ (∑ i ∈ I, t i + 1) ^ D + 3 ^ D := (prefactor_sum_aux hD t I ht).2 hcard
    _ ≤ (s + 1) ^ D + 3 ^ D := by
      gcongr

/-- Equation `eq:main-orbit-slack`, second inequality: for `s ≥ 6` and `D ≥ 3`,
`(s+2)^D - (s+1)^D - 3^D ≥ (D/2) s^(D-1)`. -/
theorem eq_main_orbit_slack_gap {D : ℕ} (hD : 3 ≤ D) {s : ℝ} (hs : 6 ≤ s) :
    (D / 2 : ℝ) * s ^ (D - 1) ≤ (s + 2) ^ D - (s + 1) ^ D - 3 ^ D := by
  obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hm : 2 ≤ m := by omega
  -- `(s+2)^D - (s+1)^D ≥ D (s+1)^(D-1) ≥ D s^(D-1)`.
  have hdiff : ((m + 1 : ℕ) : ℝ) * s ^ m ≤ (s + 2) ^ (m + 1) - (s + 1) ^ (m + 1) := by
    rw [← geom_sum₂_mul]
    have e : s + 2 - (s + 1) = 1 := by ring
    rw [e, mul_one]
    calc ((m + 1 : ℕ) : ℝ) * s ^ m = ∑ i ∈ range (m + 1), s ^ i * s ^ (m + 1 - 1 - i) := by
          rw [sum_congr rfl (g := fun _ => s ^ m)]
          · simp
          · intro i hi
            rw [← pow_add]; congr 1; simp at hi; omega
      _ ≤ _ := by
          apply sum_le_sum; intro i _
          apply mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) _)
            (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity) (by positivity)
  -- `3^D ≤ (D/2) s^(D-1)`, since `3^D 2^(D-1) = 3·6^(D-1) ≤ 3 s^(D-1)` and `2^(D-1) ≥ 4`.
  have h6 : (6 : ℝ) ^ m ≤ s ^ m := pow_le_pow_left₀ (by norm_num) hs m
  have h2 : (4 : ℝ) ≤ 2 ^ m := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have e6 : (6 : ℝ) ^ m = 3 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  have h3 : (3 : ℝ) ^ (m + 1) * 4 ≤ 3 * s ^ m := by
    rw [pow_succ]
    have : (3 : ℝ) ^ m * 4 ≤ 3 ^ m * 2 ^ m := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hmr : (3 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 1)
  have hsm : 0 ≤ s ^ m := by positivity
  nlinarith

/-! ## Equation (main-cap-payment) -/

/-- Equation `eq:main-cap-payment`. An interval of ratio `d` whose old cap `c_old` is
at least `q` (and at most `d`, as every stored cap is) gets a new cap `c_new ≤ βq`,
where `βq ≥ 2`. Its contribution `(log d) log max{c,2}` to `Q` drops by at least
`(log d) log(1/β)`, and this is at least `c_β log q` with `c_β = log(1/β)`. -/
theorem eq_main_cap_payment {d q β cOld cNew : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβq : 2 ≤ β * q) (hq : q ≤ cOld) (hcd : cOld ≤ d) (hcNew : cNew ≤ β * q) :
    Real.log d * Real.log (1 / β) ≤
      Real.log d * Real.log (max cOld 2) - Real.log d * Real.log (max cNew 2) ∧
    Real.log (1 / β) * Real.log q ≤ Real.log d * Real.log (1 / β) := by
  have hq2 : 2 ≤ q := by nlinarith
  have hold : max cOld 2 = cOld := max_eq_left (by linarith)
  have hnew : max cNew 2 ≤ β * q := max_le hcNew hβq
  have hd0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hb0 : 0 ≤ Real.log (1 / β) := Real.log_nonneg (by rw [le_div_iff₀ hβ0]; linarith)
  have hlogβ : Real.log (1 / β) = Real.log q - Real.log (β * q) := by
    rw [Real.log_mul hβ0.ne' (by linarith), one_div, Real.log_inv]; ring
  constructor
  · rw [hold, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ hd0
    have h1 : Real.log q ≤ Real.log cOld := Real.log_le_log (by linarith) hq
    have h2 : Real.log (max cNew 2) ≤ Real.log (β * q) :=
      Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hnew
    linarith
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (by linarith) (hq.trans hcd)) hb0
