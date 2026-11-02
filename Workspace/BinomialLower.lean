import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace GI

/-- Cover every function by a t-element set containing its range. Counting
this surjection gives the elementary lower bound for binomial coefficients. -/
theorem power_le_choose_mul_power {m t : ℕ} (htm : t ≤ m) :
    m ^ t ≤ m.choose t * t ^ t := by
  classical
  let T := {s : Finset (Fin m) // s.card = t}
  let cover : (Σ s : T, Fin t → {x // x ∈ s.val}) → (Fin t → Fin m) :=
    fun z i => (z.2 i).val
  have onto : Function.Surjective cover := by
    intro f
    have hr : (Finset.univ.image f).card ≤ t := by
      simpa using (Finset.card_image_le (s := Finset.univ) (f := f))
    obtain ⟨s, hrs, hst⟩ := Finset.exists_superset_card_eq hr
      (by simpa using htm)
    refine ⟨⟨⟨s, hst⟩, fun i => ⟨f i, hrs ?_⟩⟩, rfl⟩
    exact Finset.mem_image_of_mem f (Finset.mem_univ i)
  have hc := Fintype.card_le_of_surjective cover onto
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  have hs : ∀ s : T, Fintype.card {x // x ∈ s.val} = t := by
    intro s
    simpa only [Fintype.card_coe] using s.property
  simp_rw [hs] at hc
  have hT : Fintype.card T = m.choose t := by
    simpa only [T, Fintype.card_fin] using (Fintype.card_finset_len (α := Fin m) t)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hT] using hc

theorem choose_log_lower {m t : ℕ} (ht : 0 < t) (htm : t ≤ m) :
    (t : ℝ) * Real.log ((m : ℝ) / t) ≤ Real.log (m.choose t : ℝ) := by
  have hm : 0 < m := ht.trans_le htm
  have hp : 0 < m.choose t := Nat.choose_pos htm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpR : (0 : ℝ) < m.choose t := by exact_mod_cast hp
  have hpow : (m : ℝ) ^ t ≤ (m.choose t : ℝ) * (t : ℝ) ^ t := by
    exact_mod_cast power_le_choose_mul_power htm
  have hlog := Real.log_le_log (pow_pos hmR t) hpow
  rw [Real.log_mul (ne_of_gt hpR) (ne_of_gt (pow_pos htR t)), Real.log_pow,
    Real.log_pow] at hlog
  rw [Real.log_div (ne_of_gt hmR) (ne_of_gt htR)]
  nlinarith

end GI
