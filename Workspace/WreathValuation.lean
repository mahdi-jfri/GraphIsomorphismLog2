module

public import Workspace.PrimitiveSocleBudget

@[expose] public section

/-!
# The valuation estimate for groups inside a wreath product of automorphism groups

Paper, proof of Lemma A.8, the paragraph on `eq:budget-diagonal-degree`:
`v_3(|G|) ≤ s log_3 |Aut T| + v_3(s!) = O(s log |T| + s) = O(log n)`.
We prove the numerical core once, for possibly different simple factors, so that
it serves both the paper's homogeneous wreath product and the actual socle of a
radical-free primitive group.
-/

namespace GI.WreathValuation

/-- The constant of the regular/diagonal case of Lemma A.8. -/
noncomputable def diagonalConstant : ℝ := 24 / Real.log 3 + 6 / Real.log 2

/-- Numerical core. Here `a` is the group order, `P` the product of the
automorphism-group orders, `s` the number of factors and `Q` the product of the
factor orders. The hypotheses are: `a ∣ P · s!` (the group lies in the wreath
product), `P ≤ Q^2` (from `|Aut T| ≤ |T|^2`), `Q ≤ n^2` (the degree bound
`n ≥ |T|^{s/2}`), and `2^s ≤ Q` (each factor has order at least two). -/
theorem three_valuation_le_of_dvd {a P s Q n : ℕ} (ha : a ∣ P * s.factorial)
    (hP0 : 0 < P) (hP : P ≤ Q ^ 2) (hQ : Q ≤ n ^ 2) (hs : 2 ^ s ≤ Q) :
    6 * (padicValNat 3 a : ℝ) ≤ diagonalConstant * Real.log n := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hs
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hQ; omega
    · exact h
  have hprod0 : P * s.factorial ≠ 0 := Nat.mul_ne_zero hP0.ne' (Nat.factorial_ne_zero s)
  -- `v_3(a) ≤ v_3(P) + v_3(s!)`, since `a` divides `P · s!`.
  have hv : padicValNat 3 a ≤ padicValNat 3 P + padicValNat 3 s.factorial := by
    have := GI.primeValuation_mono (p := 3) hprod0 ha
    rwa [padicValNat.mul hP0.ne' (Nat.factorial_ne_zero s)] at this
  -- Legendre: `2 v_3(s!) ≤ s`.
  have hleg := sub_one_mul_padicValNat_factorial (p := 3) s
  have hfact : 2 * padicValNat 3 s.factorial ≤ s := by
    have := Nat.sub_le s ((3 : ℕ).digits s).sum
    norm_num only at hleg
    omega
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- `log Q ≤ 2 log n`.
  have hlogQ : Real.log Q ≤ 2 * Real.log n := by
    have h := Real.log_le_log (by exact_mod_cast hQ0) (show (Q : ℝ) ≤ (n : ℝ) ^ 2 by
      exact_mod_cast hQ)
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  -- `v_3(P) log 3 ≤ log P ≤ 2 log Q`.
  have hvP : (padicValNat 3 P : ℝ) * Real.log 3 ≤ 4 * Real.log n := by
    have h1 := GI.SocleOuter.valuation_log_bound (p := 3) (by norm_num) hP0
    have h2 := Real.log_le_log (by exact_mod_cast hP0) (show (P : ℝ) ≤ (Q : ℝ) ^ 2 by
      exact_mod_cast hP)
    rw [Real.log_pow] at h2
    push_cast at h1 h2
    linarith
  -- `s log 2 ≤ log Q`.
  have hsQ : (s : ℝ) * Real.log 2 ≤ 2 * Real.log n := by
    have h := Real.log_le_log (by positivity) (show ((2 : ℝ)) ^ s ≤ (Q : ℝ) by
      exact_mod_cast hs)
    rw [Real.log_pow] at h
    linarith
  have hvR : (padicValNat 3 a : ℝ) ≤ padicValNat 3 P + padicValNat 3 s.factorial := by
    exact_mod_cast hv
  have hfR : 2 * (padicValNat 3 s.factorial : ℝ) ≤ s := by exact_mod_cast hfact
  have e1 : (padicValNat 3 P : ℝ) ≤ 4 * Real.log n / Real.log 3 := by
    rw [le_div_iff₀ hlog3]; exact hvP
  have e2 : (s : ℝ) ≤ 2 * Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; exact hsQ
  have expand : diagonalConstant * Real.log n =
      6 * (4 * Real.log n / Real.log 3) + 3 * (2 * Real.log n / Real.log 2) := by
    unfold diagonalConstant; ring
  rw [expand]
  linarith

end GI.WreathValuation
