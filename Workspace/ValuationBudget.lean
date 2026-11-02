import Workspace.FiniteBudget
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace GI

theorem primeValuation_mono {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (hab : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp (pow_padicValNat_dvd.trans hab)

theorem factorial_primeValuation_lower (p k : ℕ) [Fact p.Prime] :
    k / p ≤ padicValNat p k.factorial := by
  have h := padicValNat_factorial_mul (p := p) (k / p)
  rw [padicValNat_mul_div_factorial] at h
  omega

theorem alternating_odd_primeValuation {p k : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hk : 2 ≤ k) :
    padicValNat p (Nat.card (alternatingGroup (Fin k))) = padicValNat p k.factorial := by
  haveI : Nontrivial (Fin k) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < k by omega))
  have hc := two_mul_card_alternatingGroup (α := Fin k)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hc
  have hv := congrArg (padicValNat p) hc
  rw [padicValNat.mul (by decide) (Nat.ne_of_gt Nat.card_pos)] at hv
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [padicValNat_primes hp, zero_add] at hv
  exact hv

theorem alternating_weight_valuation {p k : ℕ} (hp : p = 3 ∨ p = 5) (hk : 64 ≤ k) :
    k ≤ 6 * padicValNat p (Nat.card (alternatingGroup (Fin k))) := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  have hn : p ≠ 2 := by rcases hp with rfl | rfl <;> decide
  rw [alternating_odd_primeValuation hn (by omega)]
  have h := factorial_primeValuation_lower p k
  have hdiv : k ≤ 6 * (k / p) := by rcases hp with rfl | rfl <;> omega
  omega

variable {V : Type*} [Fintype V]

theorem visible_primeValuation_add {p : ℕ} [Fact p.Prime]
    {a : V} {H L : Subgroup (Equiv.Perm V)} {k : ℕ}
    (step : VisibleStep a H L k) :
    padicValNat p (Nat.card H) = padicValNat p (Nat.card L) +
      padicValNat p (Nat.card (alternatingGroup (Fin k))) := by
  rw [← visible_card_factorization step]
  exact padicValNat.mul (Nat.ne_of_gt Nat.card_pos) (Nat.ne_of_gt Nat.card_pos)

/-- Equation (23): the actual chain's total marked weight is bounded by either
the 3-adic or 5-adic valuation of the group's order. -/
theorem marked_chain_valuation_bound {p cutoff w : ℕ}
    (hp : p = 3 ∨ p = 5) (hcutoff : 64 ≤ cutoff)
    {a : V} {H : Subgroup (Equiv.Perm V)} (hw : MarkedChain cutoff a H w) :
    w ≤ 6 * padicValNat p (Nat.card H) := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  induction hw with
  | stop H => exact Nat.zero_le _
  | restrict hle _ ih =>
    have hm := primeValuation_mono (p := p) (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.card_dvd_of_le hle)
    omega
  | mark hk step _ ih =>
    have hweight := alternating_weight_valuation hp (hcutoff.trans hk)
    have hsum := visible_primeValuation_add (p := p) step
    omega

theorem sigma_valuation_bound {p cutoff : ℕ}
    (hp : p = 3 ∨ p = 5) (hcutoff : 64 ≤ cutoff)
    (a : V) (H : Subgroup (Equiv.Perm V)) :
    sigma cutoff a H ≤ 6 * padicValNat p (Nat.card H) :=
  marked_chain_valuation_bound hp hcutoff (sigma_achieved (by omega) a H)

end GI
