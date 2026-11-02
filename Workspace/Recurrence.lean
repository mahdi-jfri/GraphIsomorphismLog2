import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GI

/-- A recurrence solver including the `1 + F(child)` term. All size reduction and
runtime-recurrence obligations are explicit hypotheses, not assertions about Algorithm 4. -/
theorem contracting_recurrence_bound
    (F score : ℕ → ℝ) (child : ℕ → ℕ) (base : ℕ) (C D r : ℝ)
    (hD : 0 ≤ D) (hscore : ∀ n, 0 ≤ score n)
    (hpay : C + D * r + Real.log 2 ≤ D)
    (hbase : ∀ n < base, F n ≤ Real.exp (D * score n))
    (hstep : ∀ n, base ≤ n →
      child n < n ∧ 1 ≤ score n ∧ score (child n) ≤ r * score n ∧
      F n ≤ Real.exp (C * score n) * (1 + F (child n))) :
    ∀ n, F n ≤ Real.exp (D * score n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < base
    · exact hbase n hn
    · obtain ⟨hchild, hs, hc, hrec⟩ := hstep n (Nat.le_of_not_gt hn)
      have hi := ih (child n) hchild
      have hexp : 1 ≤ Real.exp (D * score (child n)) :=
        Real.one_le_exp (mul_nonneg hD (hscore _))
      have hln : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have hlns : Real.log (2 : ℝ) ≤ Real.log 2 * score n := by
        nlinarith
      have hchildD : D * score (child n) ≤ D * (r * score n) :=
        mul_le_mul_of_nonneg_left hc hD
      have hp := mul_le_mul_of_nonneg_right hpay (hscore n)
      have he : C * score n + D * score (child n) + Real.log 2 ≤ D * score n := by
        nlinarith
      calc
        F n ≤ Real.exp (C * score n) * (1 + F (child n)) := hrec
        _ ≤ Real.exp (C * score n) * (2 * Real.exp (D * score (child n))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith
        _ = Real.exp (C * score n + D * score (child n) + Real.log 2) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
        _ ≤ Real.exp (D * score n) := Real.exp_le_exp.mpr he

noncomputable def logSquare (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 2)) ^ 2

/-- The final scalar implication of equation (17), using a contracted logarithmic square.
Establishing this recurrence for the proposed algorithm is still a separate obligation. -/
theorem phase_recurrence_bound (F : ℕ → ℝ) (child : ℕ → ℕ)
    (base : ℕ) (C D r : ℝ) (hD : 0 ≤ D)
    (hpay : C + D * r + Real.log 2 ≤ D)
    (hbase : ∀ n < base, F n ≤ Real.exp (D * logSquare n))
    (hstep : ∀ n, base ≤ n → child n < n ∧ 1 ≤ logSquare n ∧
      logSquare (child n) ≤ r * logSquare n ∧
      F n ≤ Real.exp (C * logSquare n) * (1 + F (child n))) :
    ∀ n, F n ≤ Real.exp (D * logSquare n) :=
  contracting_recurrence_bound F logSquare child base C D r hD
    (fun _ => sq_nonneg _) hpay hbase hstep

theorem explicit_recurrence_coefficient {C r : ℝ} (hC : 0 ≤ C)
    (hr : r < 1) :
    let D := (C + Real.log 2) / (1 - r)
    0 ≤ D ∧ C + D * r + Real.log 2 ≤ D := by
  dsimp
  have hd : 0 < 1 - r := sub_pos.mpr hr
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  constructor
  · exact div_nonneg (add_nonneg hC hl) hd.le
  · have hh := div_mul_cancel₀ (C + Real.log 2) (ne_of_gt hd)
    nlinarith

/-- Passing from `n` vertices to `n²` positions preserves a quadratic logarithmic exponent. -/
theorem graph_logSquare_bound (n : ℕ) : logSquare (n ^ 2) ≤ 4 * logSquare n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hleft : 0 ≤ Real.log ((n : ℝ) ^ 2 + 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (n : ℝ)])
  have hright : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlog : Real.log ((n : ℝ) ^ 2 + 2) ≤
      2 * Real.log ((n : ℝ) + 2) := by
    calc
      Real.log ((n : ℝ) ^ 2 + 2) ≤ Real.log (((n : ℝ) + 2) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log ((n : ℝ) + 2) := by rw [Real.log_pow]; norm_num
  dsimp [logSquare]
  push_cast
  nlinarith [sq_nonneg (2 * Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) ^ 2 + 2))]

theorem graph_exponent_bound (n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (D * logSquare (n ^ 2)) ≤ Real.exp ((4 * D) * logSquare n) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (graph_logSquare_bound n) hD
  nlinarith

end GI
