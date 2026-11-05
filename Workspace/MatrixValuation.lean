module

public import Workspace.ValuationBudget
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace GI.MatrixValuation

open scoped BigOperators

/-- The actual multiplicative order of the residue of `q` modulo `p`. -/
noncomputable def residueOrder (p q : ℕ) : ℕ := orderOf (q : ZMod p)

variable {p q : ℕ} [hp : Fact p.Prime]

theorem residueOrder_pos (hq : ¬p ∣ q) : 0 < residueOrder p q := by
  have hz : (q : ZMod p) ≠ 0 := by
    exact fun h => hq ((ZMod.natCast_eq_zero_iff q p).mp h)
  have hd := ZMod.orderOf_dvd_card_sub_one hz
  change residueOrder p q ∣ p - 1 at hd
  have hp2 := hp.out.two_le
  by_contra hn
  have he : residueOrder p q = 0 := Nat.eq_zero_of_not_pos hn
  rw [he, zero_dvd_iff] at hd
  omega

theorem prime_dvd_pow_sub_one_iff (hq : 1 < q) (j : ℕ) :
    p ∣ q ^ j - 1 ↔ residueOrder p q ∣ j := by
  have hpow : 1 ≤ q ^ j := one_le_pow₀ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpow,
    Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one.symm

theorem valuation_pow_sub_one_of_order_dvd (hodd : Odd p) (hq : 1 < q)
    (hpq : ¬p ∣ q) {j : ℕ} (hj : 0 < j) (he : residueOrder p q ∣ j) :
    padicValNat p (q ^ j - 1) =
      padicValNat p (q ^ residueOrder p q - 1) + padicValNat p (j / residueOrder p q) := by
  let e := residueOrder p q
  have hepos : 0 < e := residueOrder_pos hpq
  have hpower : 1 < q ^ e := one_lt_pow₀ hq (by omega)
  have hdiv : p ∣ q ^ e - 1 := (prime_dvd_pow_sub_one_iff hq e).2 dvd_rfl
  have hcoprime : ¬p ∣ q ^ e := fun h => hpq (hp.out.dvd_of_dvd_pow h)
  have hu : j / e ≠ 0 := by
    have hle : e ≤ j := Nat.le_of_dvd hj he
    exact Nat.ne_of_gt (Nat.div_pos hle hepos)
  have hlte := padicValNat.pow_sub_pow hodd hpower hdiv hcoprime hu
  simp only [one_pow] at hlte
  rw [← pow_mul, Nat.mul_div_cancel' he] at hlte
  exact hlte

theorem valuation_pow_sub_one_of_order_not_dvd (hq : 1 < q) {j : ℕ}
    (he : ¬residueOrder p q ∣ j) : padicValNat p (q ^ j - 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => he ((prime_dvd_pow_sub_one_iff hq j).1 h))

/-- Summing the actual valuations at the multiples of the residue order
produces the factorial term; no valuation formula is assumed. -/
theorem valuation_sum (hodd : Odd p) (hq : 1 < q) (hpq : ¬p ∣ q) (d : ℕ) :
    (∑ j ∈ Finset.range d, padicValNat p (q ^ (j + 1) - 1)) =
      (d / residueOrder p q) * padicValNat p (q ^ residueOrder p q - 1) +
        padicValNat p (d / residueOrder p q).factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases he : residueOrder p q ∣ d + 1
    · have hf : padicValNat p (d / residueOrder p q + 1).factorial =
          padicValNat p (d / residueOrder p q + 1) +
            padicValNat p (d / residueOrder p q).factorial := by
        rw [Nat.factorial_succ]
        exact padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)
      rw [valuation_pow_sub_one_of_order_dvd hodd hq hpq (by omega) he,
        Nat.succ_div_of_dvd he, hf]
      ring
    · rw [valuation_pow_sub_one_of_order_not_dvd hq he, Nat.succ_div_of_not_dvd he]
      omega

theorem valuation_finset_prod {A : Type*} (s : Finset A) (f : A → ℕ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    padicValNat p (∏ a ∈ s, f a) = ∑ a ∈ s, padicValNat p (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (Finset.mem_insert_of_mem hb))),
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

theorem valuation_order_factor (hq : 1 < q) (hpq : ¬p ∣ q) {i d : ℕ} (hi : i < d) :
    padicValNat p (q ^ d - q ^ i) = padicValNat p (q ^ (d - i) - 1) := by
  have hfactor : q ^ d - q ^ i = (q ^ (d - i) - 1) * q ^ i := by
    rw [Nat.sub_mul, one_mul, Nat.pow_sub_mul_pow q hi.le]
  have hsub : q ^ (d - i) - 1 ≠ 0 := by
    have hpow : 1 < q ^ (d - i) := one_lt_pow₀ hq (by omega)
    omega
  rw [hfactor, padicValNat.mul hsub (pow_ne_zero _ (by omega)),
    padicValNat.pow, padicValNat.eq_zero_of_not_dvd hpq]
  simp

theorem valuation_order_product (hq : 1 < q) (hpq : ¬p ∣ q) (d : ℕ) :
    padicValNat p (∏ i : Fin d, (q ^ d - q ^ (i : ℕ))) =
      ∑ j ∈ Finset.range d, padicValNat p (q ^ (j + 1) - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => q ^ d - q ^ i) d, valuation_finset_prod]
  · calc
      (∑ i ∈ Finset.range d, padicValNat p (q ^ d - q ^ i)) =
          ∑ i ∈ Finset.range d, padicValNat p (q ^ (d - i) - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact valuation_order_factor hq hpq (Finset.mem_range.mp hi)
      _ = ∑ i ∈ Finset.range d, padicValNat p (q ^ (i + 1) - 1) := by
        rw [← Finset.sum_range_reflect (fun i => padicValNat p (q ^ (d - i) - 1)) d]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have he : d - (d - 1 - i) = i + 1 := by omega
        rw [he]
  · intro i hi
    have hpow : q ^ i < q ^ d := Nat.pow_lt_pow_right hq (Finset.mem_range.mp hi)
    omega

/-- The matrix valuation formula in A.8 for the cardinality of the actual
general linear group over a finite field. -/
theorem generalLinearGroup_valuation {F : Type*} [Field F] [Fintype F]
    (hodd : Odd p) (hpq : ¬p ∣ Fintype.card F) (d : ℕ) :
    padicValNat p (Nat.card (GL (Fin d) F)) =
      (d / residueOrder p (Fintype.card F)) *
        padicValNat p ((Fintype.card F) ^ residueOrder p (Fintype.card F) - 1) +
      padicValNat p (d / residueOrder p (Fintype.card F)).factorial := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_GL_field, valuation_order_product hq hpq, valuation_sum hodd hq hpq]

end GI.MatrixValuation
