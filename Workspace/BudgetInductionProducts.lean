import Workspace.BudgetInductionBasic
import Workspace.CartesianHereditary
import Workspace.JohnsonBound

namespace GI.BudgetInduction

open scoped BigOperators

theorem component_degree_lt {d s : ℕ} (hd : 2 ≤ d) (hs : 2 ≤ s) : d < d ^ s := by
  simpa only [pow_one] using
    (pow_lt_pow_right₀ (by omega : 1 < d) (by omega : 1 < s))

/-- Cartesian charging, including the actual zero component budget at
degree two, with the exact constants from A.9. -/
theorem allowance_power {C : ℝ} (hC : 128 ≤ C) {d s : ℕ}
    (hd : 2 ≤ d) (hs : 2 ≤ s) :
    (3 * (s - 1) : ℕ) + (s : ℝ) * degreeAllowance C d ≤ degreeAllowance C (d ^ s) := by
  have hn : 3 ≤ d ^ s := by have h := component_degree_lt hd hs; omega
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hC0 : 0 ≤ C := by linarith
  rw [allowance_large C hn, Nat.cast_pow, Real.log_pow]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
  by_cases hd2 : d ≤ 2
  · have he : d = 2 := by omega
    rw [allowance_small C hd2, mul_zero, add_zero, he]
    norm_num only [Nat.cast_ofNat]
    have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by
      have h := Johnson.log_two_lower
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog hC0
    have hpositive : 0 ≤ C * Real.log 2 - 3 := by nlinarith
    have hstep := mul_le_mul_of_nonneg_right hsR hpositive
    nlinarith
  · rw [allowance_large C (by omega)]
    nlinarith

/-- The actual Cartesian action and every component representation satisfy
the induction bound; no transitivity or independence premise is needed. -/
theorem sigma_cartesian {I D : Type*} [Fintype I] [Fintype D] [Fintype (I → D)]
    {cutoff : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (ih : ∀ m < Fintype.card (I → D), ∀ b : Fin m,
      (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    {H : Subgroup (Equiv.Perm (I → D))} (c : CartesianCover H) (v : I → D)
    (hd : 2 ≤ Fintype.card D) (hs : 2 ≤ Fintype.card I) :
    (sigma cutoff v H : ℝ) ≤ degreeAllowance C (Fintype.card (I → D)) := by
  classical
  have hcard : Fintype.card (I → D) = (Fintype.card D) ^ Fintype.card I := by
    simpa only [Nat.card_eq_fintype_card] using (Nat.card_fun (α := I) (β := D))
  have hdlt : Fintype.card D < Fintype.card (I → D) := by
    rw [hcard]
    exact component_degree_lt hd hs
  have hc : ∀ i : I, (sigma cutoff (v i) (c.component i).range : ℝ) ≤
      degreeAllowance C (Fintype.card D) :=
    fun i => sigma_le_of_smaller_degree (by omega) ih hdlt (c.component i).range (v i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
  have hsplit := c.sigma_cartesian_le hcutoff v
  have hsplitR : (sigma cutoff v H : ℝ) ≤ (3 * (Fintype.card I - 1) : ℕ) +
      ∑ i, (sigma cutoff (v i) (c.component i).range : ℝ) := by exact_mod_cast hsplit
  have hsum' : (∑ i, (sigma cutoff (v i) (c.component i).range : ℝ)) ≤
      (Fintype.card I : ℝ) * degreeAllowance C (Fintype.card D) := by simpa using hsum
  rw [hcard]
  exact (hsplitR.trans (add_le_add_right hsum' _)).trans (allowance_power hC hd hs)

/-- Every nonnatural Johnson domain has larger degree than its natural
underlying set; this supplies the strict induction comparison. -/
theorem natural_degree_lt_johnson {m t : ℕ} (ht : 2 ≤ t) (hhalf : 2 * t ≤ m) :
    m < m.choose t := by
  have hmono : ∀ r, 2 ≤ r → r ≤ m / 2 → m.choose 2 ≤ m.choose r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => intro _; rfl
    | succ r hr ih =>
        intro h
        exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have h := hmono t ht (by omega)
  have htwo := Nat.choose_succ_right_eq m 1
  simp only [Nat.choose_one_right, Nat.reduceAdd] at htwo
  have hm : 4 ≤ m := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hstrict : m < m.choose 2 := by nlinarith
  exact hstrict.trans_le h

/-- A.7's natural-action premise is discharged by the actual strong
induction hypothesis. Every subgroup of the full subset image is covered. -/
theorem sigma_johnson {m t cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C) (ht : 2 ≤ t) (hhalf : 2 * t ≤ m)
    (ih : ∀ r < Fintype.card (Johnson.SubsetVertex (Fin m) t), ∀ b : Fin r,
      (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C r)
    (H : Subgroup (Equiv.Perm (Johnson.SubsetVertex (Fin m) t)))
    (hH : H ≤ Johnson.subsetImage t) (s : Johnson.SubsetVertex (Fin m) t) :
    (sigma cutoff s H : ℝ) ≤ degreeAllowance C (Fintype.card (Johnson.SubsetVertex (Fin m) t)) := by
  have hn := natural_degree_lt_johnson ht hhalf
  have hnat : Johnson.NaturalActionBound cutoff C (C + 6) m := by
    intro r hr hrm b
    have h := ih r (by rw [Johnson.card_subsetVertex_fin]; exact hrm.trans_lt hn) b
    rwa [allowance_large C hr] at h
  have hb := Johnson.johnson_anchor_bound hcutoff hC ht hhalf hnat s
  have hmono : (sigma cutoff s H : ℝ) ≤ sigma cutoff s (Johnson.subsetImage t) :=
    Nat.cast_le.mpr (sigma_subgroup_mono (by omega) s hH)
  rw [Johnson.card_subsetVertex_fin, allowance_large C (by omega)]
  exact hmono.trans hb

end GI.BudgetInduction
