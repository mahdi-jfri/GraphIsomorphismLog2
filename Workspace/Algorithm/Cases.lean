import Workspace.Algorithm.Interfaces
import Workspace.Paper.SupportThresholds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Why the cases cover every large action (Section 6.2)

"For `q > λ` and sufficiently large `N`, we have `C(q,3) > N`. Also `q` exceeds the
logarithmic transitive-kernel threshold. The support classification therefore
gives precisely the one-label and two-label cases. An action with transitive kernel
on the whole active domain is excluded at this scale.

In the natural case, the row partition is already an interval of the retained
hierarchy. Indeed, a selected Johnson constituent has `C(q,a) ≥ q` physical blocks,
all fixed by the giant kernel. The support classification gives exactly `q` kernel
orbits, so there are exactly `q` physical blocks and `a = 1`. …

The row size is at most `N^{1-α}`. Since `1-α < 2α < γ`, the row terminal makes
only fresh calls below the phase threshold. In an intransitive row variation, the
number of columns is also at most `N^{1-α}`. Any later column giant of degree
`q > λ` must be natural, since even its unordered-pair action would require
`C(q,2) > N^{1-α}` columns."

Each claim is proved below, under `1/3 < α < 1/2` and `2α < γ` (eq.
`scale-constraints`):

* `choose_three_gt`, `log_threshold_lt`: the two size facts;
* `large_giant_support_cases`: Corollary A.25 then gives the one-label,
  ordered-pair and unordered-pair cases;
* `johnson_level_eq_one`: `C(q,a) = q` with `1 ≤ a ≤ q/2` and `q ≥ 4` forces `a = 1`;
* `row_size_lt`, `exponent_order`: the row size and the exponents;
* `column_giant_natural`: `C(q,2) > N^{1-α}` for `q > N^α`;
* `giantStep_cases`: in `GiantStep`, a large action that is not sent to `RowStep`
  has a two-label kernel-orbit map or a retained row action of degree at least `q`
  (the two inherited rectangle representations of Sections 5.2 and 5.3).
-/

namespace GI.Algorithm

open Filter Real

/-- For a positive exponent `e`, `N^e` eventually exceeds any bound. -/
theorem eventually_rpow_ge {e : ℝ} (he : 0 < e) (M : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → M ≤ (N : ℝ) ^ e := by
  have h := ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₁, fun N hN => hN₁ N hN⟩

/-- **"For `q > λ` and sufficiently large `N`, we have `C(q,3) > N`."** -/
theorem choose_three_gt {α : ℝ} (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ q : ℕ, (N : ℝ) ^ α < q → N < q.choose 3 := by
  obtain ⟨N₁, hN₁⟩ := eventually_rpow_ge (show 0 < 3 * α - 1 by linarith) 48
  obtain ⟨N₂, hN₂⟩ := eventually_rpow_ge (show 0 < α by linarith) 4
  refine ⟨max (max N₁ N₂) 1, fun N hN q hq => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have h48 := hN₁ N hN1
  have h4 := hN₂ N hN2
  have hq4 : (4 : ℝ) < q := lt_of_le_of_lt h4 hq
  -- `N^{3α} = N · N^{3α-1} ≥ 48 N`.
  have hpow : (N : ℝ) ^ (3 * α) = N * (N : ℝ) ^ (3 * α - 1) := by
    rw [← Real.rpow_one_add' hNpos.le (by linarith)]
    · ring_nf
  have hq3 : (N : ℝ) ^ (3 * α) < (q : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * α = α * 3 by ring, Real.rpow_mul hNpos.le]
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ α := Real.rpow_nonneg hNpos.le _
    have : ((N : ℝ) ^ α) ^ (3 : ℝ) = ((N : ℝ) ^ α) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast _ 3
    rw [this]
    exact pow_lt_pow_left₀ hq h0 (by norm_num)
  -- `6 C(q,3) = q(q-1)(q-2) ≥ q³/4` for `q ≥ 4`.
  have hchoose : ((q.choose 3 : ℕ) : ℝ) * 6 = q * (q - 1) * (q - 2) := by
    have hq3' : 3 ≤ q := by exact_mod_cast (show (3 : ℝ) ≤ q by linarith)
    have h := Nat.choose_mul_factorial_mul_factorial hq3'
    have hfac : ((q - 3).factorial : ℝ) * ((q - 2) * (q - 1) * q) = (q.factorial : ℝ) := by
      have e : q = (q - 3) + 1 + 1 + 1 := by omega
      conv_rhs => rw [e]
      push_cast [Nat.factorial_succ]
      have h1 : ((q - 3 : ℕ) : ℝ) = (q : ℝ) - 3 := by rw [Nat.cast_sub hq3']; norm_num
      rw [h1]
      ring
    have h' : ((q.choose 3 : ℕ) : ℝ) * 6 * ((q - 3).factorial : ℝ) = q.factorial := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast [Nat.factorial] at this
      linarith
    have hpos : (0 : ℝ) < ((q - 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have := h'.trans hfac.symm
    nlinarith [this]
  have hbound : (q : ℝ) ^ 3 ≤ 4 * (q * (q - 1) * (q - 2)) := by nlinarith
  have : (N : ℝ) * 48 < ((q.choose 3 : ℕ) : ℝ) * 24 := by
    have h1 : (N : ℝ) * 48 ≤ (N : ℝ) ^ (3 * α) := by
      rw [hpow]; exact mul_le_mul_of_nonneg_left h48 hNpos.le
    linarith
  have : (N : ℝ) < (q.choose 3 : ℕ) := by linarith
  exact_mod_cast this

/-- **"Also `q` exceeds the logarithmic transitive-kernel threshold."** For large `N`,
every `q > N^α` satisfies `q ≥ 201` (the threshold `m₀` of Lemma A.24) and
`q > max(8, 2 + log₂ s)` for every `s ≤ N` (the threshold of Lemma A.15). -/
theorem log_threshold_lt {α : ℝ} (hα : 0 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ s : ℕ, s ≤ N → ∀ q : ℕ, (N : ℝ) ^ α < q →
      201 ≤ q ∧ max 8 (2 + Real.logb 2 s) < (q : ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop hα).bound
    (show 0 < Real.log 2 / 2 by have := Real.log_pos (one_lt_two (α := ℝ)); linarith)
  have hlog' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hlog'
  obtain ⟨N₂, hN₂⟩ := eventually_rpow_ge hα 201
  refine ⟨max (max N₁ N₂) 1, fun N hN s hs q hq => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have h201 := hN₂ N hN2
  have h200 : (200 : ℝ) < q := by linarith
  have h200' : 200 < q := by exact_mod_cast h200
  refine ⟨h200', ?_⟩
  have hl := hN₁ N hN1
  simp only [Real.norm_eq_abs] at hl
  have hlogN : Real.log N ≤ Real.log 2 / 2 * (N : ℝ) ^ α := by
    have h1 : Real.log N = |Real.log N| := (abs_of_nonneg (Real.log_nonneg hNpos)).symm
    have h2 : |(N : ℝ) ^ α| = (N : ℝ) ^ α := abs_of_nonneg (Real.rpow_nonneg (by linarith) _)
    rw [h1]; rw [h2] at hl; exact hl
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogbN : Real.logb 2 N ≤ (N : ℝ) ^ α / 2 := by
    rw [Real.logb, div_le_iff₀ hlog2]
    nlinarith
  have hlogbs : Real.logb 2 s ≤ Real.logb 2 N := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg one_lt_two hNpos
    · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h) (by exact_mod_cast hs)
  refine max_lt (by linarith) ?_
  linarith

/-- **The support classification at the scale `q > λ`.** Let `G` act transitively on
the active domain `Ω` with `|Ω| ≤ N`, and let `φ : G ↠ Alt(Γ)` with `|Γ| > N^α`. For
large `N`, the kernel orbits are indexed by single labels, by ordered pairs, or by
unordered pairs of distinct labels (Corollary A.25); with fewer than `C(q,2)`
positions only single labels remain. (Section 6.2: "The support classification
therefore gives precisely the one-label and two-label cases. An action with
transitive kernel on the whole active domain is excluded at this scale.") -/
theorem large_giant_support_cases (hcite : GI.Cited.TransitiveAffected) {α : ℝ}
    (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
        (G : Subgroup (Equiv.Perm Ω)) [MulAction.IsPretransitive G Ω]
        (φ : G →* alternatingGroup Γ), Function.Surjective φ →
        Fintype.card Ω ≤ N → (N : ℝ) ^ α < Fintype.card Γ →
        (Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω Γ) ∨
          Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) ∨
          Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2))) := by
  obtain ⟨N₁, h₁⟩ := choose_three_gt hα
  obtain ⟨N₂, h₂⟩ := log_threshold_lt (show 0 < α by linarith)
  refine ⟨max N₁ N₂, fun N hN Ω Γ _ _ _ _ G _ φ hφ hΩ hΓ => ?_⟩
  have hc3 := h₁ N (le_trans (le_max_left _ _) hN) _ hΓ
  obtain ⟨h201, hlog⟩ := h₂ N (le_trans (le_max_right _ _) hN) _ hΩ _ hΓ
  exact (GI.Paper.cor_physical_support_thresholds hcite G φ hφ h201 (by omega) hlog).1

/-- **"`a = 1`."** A Johnson level `a` with `1 ≤ a ≤ q/2`, `q ≥ 4`, and exactly `q`
blocks, `C(q, a) = q`, is the natural level. -/
theorem johnson_level_eq_one {q a : ℕ} (hq : 4 ≤ q) (ha : 1 ≤ a) (haq : 2 * a ≤ q)
    (hc : q.choose a = q) : a = 1 := by
  by_contra hne
  have ha2 : 2 ≤ a := by omega
  -- `C(q, a) ≥ C(q, 2)` for `2 ≤ a ≤ q/2`.
  have hmono : ∀ b, 2 ≤ b → 2 * b ≤ q → q.choose 2 ≤ q.choose b := by
    intro b hb hbq
    induction b, hb using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have h2 := hmono a ha2 haq
  have hq2 : q < q.choose 2 := by
    rw [Nat.choose_two_right]
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 4 := ⟨q - 4, by omega⟩
    rw [show r + 4 - 1 = r + 3 by omega]
    nlinarith
  omega

/-- **"The row size is at most `N^{1-α}`."** If `s ≤ N` positions are split into
`q > N^α` rows of size `f`, then `f < N^{1-α}`. -/
theorem row_size_lt {α : ℝ} {N q f : ℕ} (hN : 0 < N) (hs : f * q ≤ N)
    (hq : (N : ℝ) ^ α < q) : (f : ℝ) < (N : ℝ) ^ (1 - α) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hα0 : (0 : ℝ) < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos _
  have hsplit : (N : ℝ) ^ (1 - α) * (N : ℝ) ^ α = N := by
    rw [← Real.rpow_add hNpos]; simp
  have hfq : (f : ℝ) * q ≤ N := by exact_mod_cast hs
  rcases Nat.eq_zero_or_pos f with h0 | hf
  · subst h0; simpa using Real.rpow_pos_of_pos hNpos (1 - α)
  · have hfpos : (0 : ℝ) < f := by exact_mod_cast hf
    by_contra hcon
    push Not at hcon
    have : (N : ℝ) ^ (1 - α) * (N : ℝ) ^ α < f * q :=
      mul_lt_mul_of_nonneg_of_pos' hcon hq hα0.le hfpos
    linarith

/-- **"`1 - α < 2α < γ`."** -/
theorem exponent_order {α γ : ℝ} (hα : 1 / 3 < α) (hγ : 2 * α < γ) :
    1 - α < 2 * α ∧ 2 * α < γ := ⟨by linarith, hγ⟩

/-- **"Any later column giant of degree `q > λ` must be natural, since even its
unordered-pair action would require `C(q,2) > N^{1-α}` columns."** -/
theorem column_giant_natural {α : ℝ} (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ q : ℕ, (N : ℝ) ^ α < q →
      (N : ℝ) ^ (1 - α) < (q.choose 2 : ℕ) := by
  obtain ⟨N₁, hN₁⟩ := eventually_rpow_ge (show 0 < 3 * α - 1 by linarith) 4
  obtain ⟨N₂, hN₂⟩ := eventually_rpow_ge (show 0 < α by linarith) 2
  refine ⟨max (max N₁ N₂) 1, fun N hN q hq => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have h4 := hN₁ N hN1
  have h2 := hN₂ N hN2
  have hq2 : (2 : ℝ) < q := lt_of_le_of_lt h2 hq
  have hα0 : (0 : ℝ) ≤ (N : ℝ) ^ α := Real.rpow_nonneg hNpos.le _
  -- `N^{2α} = N^{1-α} · N^{3α-1} ≥ 4 N^{1-α}`.
  have hsplit : (N : ℝ) ^ α * (N : ℝ) ^ α = (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (3 * α - 1) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; ring_nf
  have h1a : 0 ≤ (N : ℝ) ^ (1 - α) := Real.rpow_nonneg hNpos.le _
  have hsq : (N : ℝ) ^ α * (N : ℝ) ^ α < (q : ℝ) * q := mul_self_lt_mul_self hα0 hq
  have hc : ((q.choose 2 : ℕ) : ℝ) * 2 = q * (q - 1) := by
    rw [Nat.choose_two_right]
    have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
    have := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)
    rw [show (q * (q - 1) / 2 : ℕ) = q * (q - 1) / 2 from rfl]
    have h' : ((q * (q - 1) / 2 * 2 : ℕ) : ℝ) = ((q * (q - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub hq1] at h'
    linarith
  nlinarith

variable {Ω C : Type}

/-- **The giant-step cases.** In `GiantStep`, suppose `q > λ` and the kernel orbits
are indexed by single labels, ordered pairs, or unordered pairs. If the state is not
sent to `RowStep`, then the kernel-orbit map is not natural, or a row action of degree
at least `q` is retained. These are the two inherited rectangle representations of
Algorithm 3: the pair orbit of Section 5.2 and the row–column diagonal orbit of
Section 5.3 (Lemma A.30 needs `q ≤ m`). -/
theorem giantStep_cases {α : ℝ} (S : State Ω C) (L : GiantLabels S)
    (hq : (S.N : ℝ) ^ α < L.q) (hnot : ¬ RowCase α S L) :
    (¬ ∃ label, NaturalRows S L label) ∨ ∃ R, S.rows = some R ∧ L.q ≤ R.m := by
  by_cases hnat : ∃ label, NaturalRows S L label
  · right
    by_contra hR
    push Not at hR
    exact hnot ⟨hq, hnat, hR⟩
  · exact Or.inl hnat

end GI.Algorithm
