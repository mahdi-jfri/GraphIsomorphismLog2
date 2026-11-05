module

public import Workspace.MatrixValuation

@[expose] public section

namespace GI.MatrixValuation

variable {p q : ℕ} [hp : Fact p.Prime]

theorem valuation_pow_sub_one_log_bound (hq : 1 < q) {e : ℕ} (he : 0 < e) :
    (padicValNat p (q ^ e - 1) : ℝ) * Real.log p ≤ (e : ℝ) * Real.log q := by
  have hpow : 1 < q ^ e := one_lt_pow₀ hq (by omega)
  have hpos : 0 < q ^ e - 1 := by omega
  have hle : p ^ padicValNat p (q ^ e - 1) ≤ q ^ e :=
    (Nat.le_of_dvd hpos pow_padicValNat_dvd).trans (Nat.sub_le _ _)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hreal : (p : ℝ) ^ padicValNat p (q ^ e - 1) ≤ (q : ℝ) ^ e := by
    exact_mod_cast hle
  have hlog := Real.log_le_log (pow_pos hp0 _) hreal
  simpa only [Real.log_pow] using hlog

theorem valuation_factorial_real_bound (u : ℕ) :
    (padicValNat p u.factorial : ℝ) ≤ (u : ℝ) / (p - 1 : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hn : (p - 1) * padicValNat p u.factorial ≤ u := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hr : ((p : ℝ) - 1) * (padicValNat p u.factorial : ℝ) ≤ (u : ℝ) := by
    have hr' : ((p - 1 : ℕ) : ℝ) * (padicValNat p u.factorial : ℝ) ≤ (u : ℝ) := by
      exact_mod_cast hn
    rw [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one] at hr'
    exact hr'
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).2
  nlinarith

/-- The explicit matrix estimate in A.8, before choosing the prime. -/
theorem generalLinearGroup_valuation_bound {F : Type*} [Field F] [Fintype F]
    (hodd : Odd p) (hpq : ¬p ∣ Fintype.card F) (d : ℕ) :
    (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
      (d : ℝ) * Real.log (Fintype.card F) / Real.log p +
        (d : ℝ) / (p - 1 : ℝ) := by
  let q := Fintype.card F
  let e := residueOrder p q
  let u := d / e
  have hq : 1 < q := Fintype.one_lt_card
  have he : 0 < e := residueOrder_pos hpq
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hplog : 0 < Real.log p := Real.log_pos hp1
  have hqlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hbase := valuation_pow_sub_one_log_bound (p := p) hq he
  have humul : u * e ≤ d := Nat.div_mul_le_self d e
  have hule : u ≤ d := Nat.div_le_self d e
  have humulReal : (u : ℝ) * e ≤ d := by exact_mod_cast humul
  have huleReal : (u : ℝ) ≤ d := by exact_mod_cast hule
  have hmul := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
  have hmul' := mul_le_mul_of_nonneg_right humulReal hqlog
  have hfirst : (u : ℝ) * padicValNat p (q ^ e - 1) ≤
      (d : ℝ) * Real.log q / Real.log p := by
    apply (le_div_iff₀ hplog).2
    nlinarith
  have hsecond := (valuation_factorial_real_bound (p := p) u).trans
    (div_le_div_of_nonneg_right huleReal (by linarith : (0 : ℝ) ≤ p - 1))
  rw [generalLinearGroup_valuation hodd hpq]
  push_cast
  change (u : ℝ) * padicValNat p (q ^ e - 1) + padicValNat p u.factorial ≤ _
  exact add_le_add hfirst hsecond

/-- One uniform logarithmic estimate for the two primes used by the budget.
The degree is the actual cardinality `q^d` of the underlying vector space. -/
theorem generalLinearGroup_uniform_bound {F : Type*} [Field F] [Fintype F]
    (hprime : p = 3 ∨ p = 5) (hpq : ¬p ∣ Fintype.card F) (d : ℕ) :
    6 * (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
      (12 / Real.log 2) * Real.log ((Fintype.card F : ℝ) ^ d) := by
  have hodd : Odd p := by rcases hprime with rfl | rfl <;> decide
  have hb := generalLinearGroup_valuation_bound hodd hpq d
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpReal : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hpReal
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqReal
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx : 0 ≤ (d : ℝ) * Real.log q := mul_nonneg hd (hlog2.le.trans hlogq)
  have hfirst : (d : ℝ) * Real.log q / Real.log p ≤
      (d : ℝ) * Real.log q / Real.log 2 :=
    div_le_div_of_nonneg_left hx hlog2 hlogp
  have hsecond : (d : ℝ) / (p - 1 : ℝ) ≤ d := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).2
    nlinarith
  have hthird : (d : ℝ) ≤ (d : ℝ) * Real.log q / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    exact mul_le_mul_of_nonneg_left hlogq hd
  have hsum : (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
      2 * ((d : ℝ) * Real.log q / Real.log 2) := by
    change (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
      (d : ℝ) * Real.log q / Real.log p + (d : ℝ) / (p - 1 : ℝ) at hb
    linarith
  rw [Real.log_pow]
  change 6 * (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
    (12 / Real.log 2) * ((d : ℝ) * Real.log q)
  calc
    6 * (padicValNat p (Nat.card (GL (Fin d) F)) : ℝ) ≤
        6 * (2 * ((d : ℝ) * Real.log q / Real.log 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (12 / Real.log 2) * ((d : ℝ) * Real.log q) := by ring

end GI.MatrixValuation
