module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

/-!
# Fisher's inequality

The large clique lemma ([H, Lemma 5.2]) rests on Fisher's inequality. We prove the form we
need. Points are the elements of `ι`, blocks are the elements of `κ`, and `B z q` says that the
point `q` lies in the block `z`. If every point lies in `r` blocks and every two distinct points
lie together in `l < r` blocks, then there are at least as many blocks as points.

The proof is the usual rank argument. The rows `M_q ∈ ℚ^κ` of the incidence matrix satisfy
`‖Σ g_q M_q‖² = (r - l) Σ g_q² + l (Σ g_q)²`, so they are linearly independent.
-/

namespace GI.Proved

open Finset

/-- **Fisher's inequality.** -/
theorem designFisher {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (B : κ → ι → Prop) [∀ a b, Decidable (B a b)] (r l : ℕ) (hlr : l < r)
    (hr : ∀ q, (univ.filter fun z => B z q).card = r)
    (hl : ∀ q q', q ≠ q' → (univ.filter fun z => B z q ∧ B z q').card = l) :
    Fintype.card ι ≤ Fintype.card κ := by
  set v : ι → κ → ℚ := fun q z => if B z q then 1 else 0 with hv
  -- The inner products of the rows.
  have hinner : ∀ q q', ∑ z, v q z * v q' z = if q = q' then (r : ℚ) else l := by
    intro q q'
    have h1 : ∑ z, v q z * v q' z =
        ((univ.filter fun z => B z q ∧ B z q').card : ℚ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hv]
      by_cases a : B z q <;> by_cases b : B z q' <;> simp [a, b]
    rw [h1]
    by_cases hq : q = q'
    · subst hq
      simp only [and_self, if_true]
      exact_mod_cast hr q
    · simp only [hq, if_false]
      exact_mod_cast hl q q' hq
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hz : ∀ z, ∑ q, g q * v q z = 0 := by
      intro z
      have := congrFun hg z
      simpa [Finset.sum_apply] using this
    -- Expand the squared norm of `Σ g_q v_q`.
    have hexp : ∑ z, (∑ q, g q * v q z) * (∑ q', g q' * v q' z) =
        ((r : ℚ) - l) * ∑ q, g q * g q + (l : ℚ) * ((∑ q, g q) * (∑ q, g q)) := by
      have e1 : ∑ z, (∑ q, g q * v q z) * (∑ q', g q' * v q' z) =
          ∑ q, ∑ q', g q * g q' * ∑ z, v q z * v q' z := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q' _ => ?_
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
      rw [e1]
      simp_rw [hinner]
      have e2 : ∀ q q' : ι, g q * g q' * (if q = q' then (r : ℚ) else l) =
          (l : ℚ) * (g q * g q') + (if q = q' then ((r : ℚ) - l) * (g q * g q') else 0) := by
        intro q q'
        by_cases h : q = q' <;> simp [h] <;> ring
      simp_rw [e2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      ring_nf
    have h0 : ((r : ℚ) - l) * ∑ q, g q * g q + (l : ℚ) * ((∑ q, g q) * (∑ q, g q)) = 0 := by
      rw [← hexp]
      simp [hz]
    have hrl : (0 : ℚ) < (r : ℚ) - l := by
      have : (l : ℚ) < r := by exact_mod_cast hlr
      linarith
    have hs : 0 ≤ ∑ q, g q * g q := Finset.sum_nonneg fun q _ => mul_self_nonneg _
    have ht : 0 ≤ (l : ℚ) * ((∑ q, g q) * (∑ q, g q)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_self_nonneg _)
    have hsum : ∑ q, g q * g q = 0 := by
      have : ((r : ℚ) - l) * ∑ q, g q * g q = 0 := by linarith [mul_nonneg hrl.le hs]
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    intro q
    have := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => mul_self_nonneg (g q)).mp hsum q
      (Finset.mem_univ q)
    exact mul_self_eq_zero.mp this
  have := hli.fintype_card_le_finrank
  simpa using this

end GI.Proved
