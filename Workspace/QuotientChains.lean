import Workspace.ValuationBudget

namespace GI

variable {G : Type*} [Group G]

/-- An actual alternating quotient with its exact kernel, without any action
or transitivity requirement. Used for the coordinate-position charges. -/
structure AlternatingQuotientStep (H L : Subgroup G) (k : ℕ) where
  lower : L ≤ H
  quotient : H →* alternatingGroup (Fin k)
  onto : Function.Surjective quotient
  kernel : ∀ h : H, quotient h = 1 ↔ (h : G) ∈ L

def quotientStepKernelEquiv {H L : Subgroup G} {k : ℕ}
    (s : AlternatingQuotientStep H L k) : s.quotient.ker ≃ L where
  toFun h := ⟨h.1.1, (s.kernel h.1).1 h.2⟩
  invFun l := ⟨⟨l.1, s.lower l.2⟩, (s.kernel _).2 l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem quotient_step_card_factorization {H L : Subgroup G} {k : ℕ}
    (s : AlternatingQuotientStep H L k) :
    Nat.card L * Nat.card (alternatingGroup (Fin k)) = Nat.card H := by
  have h := s.quotient.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr s.onto] at h
  rw [Nat.card_congr (quotientStepKernelEquiv s)] at h
  simpa only [Subgroup.card_top] using h

inductive QuotientChain (cutoff : ℕ) : Subgroup G → ℕ → Prop
  | stop (H) : QuotientChain cutoff H 0
  | restrict {H L w} : L ≤ H → QuotientChain cutoff L w → QuotientChain cutoff H w
  | mark {H L w k} : cutoff ≤ k → AlternatingQuotientStep H L k →
      QuotientChain cutoff L w → QuotientChain cutoff H (w + k)

theorem quotient_chain_valuation_bound [Finite G] {p cutoff w : ℕ}
    (hp : p = 3 ∨ p = 5) (hcutoff : 64 ≤ cutoff)
    {H : Subgroup G} (chain : QuotientChain cutoff H w) :
    w ≤ 6 * padicValNat p (Nat.card H) := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  induction chain with
  | stop H => exact Nat.zero_le _
  | restrict hle _ ih =>
    have hm := primeValuation_mono (p := p) (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.card_dvd_of_le hle)
    omega
  | @mark H L w k hk s _ ih =>
    have hw := alternating_weight_valuation hp (hcutoff.trans hk)
    have hsum : padicValNat p (Nat.card H) = padicValNat p (Nat.card L) +
        padicValNat p (Nat.card (alternatingGroup (Fin k))) := by
      rw [← quotient_step_card_factorization s]
      exact padicValNat.mul (Nat.ne_of_gt Nat.card_pos) (Nat.ne_of_gt Nat.card_pos)
    omega

theorem two_mul_v3_factorial_le_pred (n : ℕ) :
    2 * padicValNat 3 n.factorial ≤ n - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hv := padicValNat_factorial_mul (p := 3) (n / 3)
    rw [padicValNat_mul_div_factorial] at hv
    by_cases hzero : n / 3 = 0
    · rw [hzero] at hv
      simp only [Nat.factorial_zero, padicValNat_one_right, add_zero] at hv
      rw [hv]
      exact Nat.zero_le _
    · have hlt : n / 3 < n := Nat.div_lt_self (by omega) (by decide)
      have hi := ih (n / 3) hlt
      omega

theorem six_v3_factorial_bound (n : ℕ) :
    6 * padicValNat 3 n.factorial ≤ 3 * (n - 1) := by
  have h := two_mul_v3_factorial_le_pred n
  omega

/-- The outer-coordinate charge in A.6, valid even when no active
coordinate orbit has a transitive kernel. -/
theorem quotient_chain_permutation_bound {s cutoff w : ℕ}
    (hcutoff : 64 ≤ cutoff) {H : Subgroup (Equiv.Perm (Fin s))}
    (chain : QuotientChain cutoff H w) : w ≤ 3 * (s - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := quotient_chain_valuation_bound (p := 3) (Or.inl rfl) hcutoff chain
  have hm := primeValuation_mono (p := 3)
    (Nat.ne_of_gt (Nat.card_pos (α := Equiv.Perm (Fin s))))
    (Subgroup.card_subgroup_dvd_card H)
  have hc : Nat.card (Equiv.Perm (Fin s)) = s.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [hc] at hm
  have hf := six_v3_factorial_bound s
  omega

theorem quotient_chain_permutation_card_bound {I : Type*} [Fintype I]
    {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {H : Subgroup (Equiv.Perm I)}
    (chain : QuotientChain cutoff H w) : w ≤ 3 * (Fintype.card I - 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := quotient_chain_valuation_bound (p := 3) (Or.inl rfl) hcutoff chain
  have hm := primeValuation_mono (p := 3)
    (Nat.ne_of_gt (Nat.card_pos (α := Equiv.Perm I)))
    (Subgroup.card_subgroup_dvd_card H)
  have hc : Nat.card (Equiv.Perm I) = (Fintype.card I).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hc] at hm
  have hf := six_v3_factorial_bound (Fintype.card I)
  omega

end GI
