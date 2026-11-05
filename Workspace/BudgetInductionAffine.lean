module

public import Workspace.BudgetInductionBasic
public import Workspace.MatrixValuationAffine

@[expose] public section

namespace GI.BudgetInduction

open MatrixValuation

variable (F : Type*) [Field F] (d : ℕ)

/-- The physical affine permutation, with its actual inverse. -/
noncomputable def affinePerm (g : AffineGroup F d) : Equiv.Perm (Fin d → F) where
  toFun v := g.left.toAdd + matrixLinearEquiv F d g.right v
  invFun v := (matrixLinearEquiv F d g.right).symm (v - g.left.toAdd)
  left_inv v := by simp
  right_inv v := by simp

/-- The concrete affine semidirect group acts on the vector space of
exactly `|F|^d` points. -/
noncomputable def affineActionHom : AffineGroup F d →* Equiv.Perm (Fin d → F) where
  toFun := affinePerm F d
  map_one' := by
    apply Equiv.ext
    intro v
    change (1 : AffineGroup F d).left.toAdd +
      matrixLinearEquiv F d (1 : AffineGroup F d).right v = v
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one]
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro v
    change (g * h).left.toAdd + matrixLinearEquiv F d (g * h).right v =
      g.left.toAdd + matrixLinearEquiv F d g.right
        (h.left.toAdd + matrixLinearEquiv F d h.right v)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      (matrixLinearEquiv F d).map_mul]
    change (g.left.toAdd + matrixLinearEquiv F d g.right h.left.toAdd) +
      matrixLinearEquiv F d g.right (matrixLinearEquiv F d h.right v) = _
    rw [map_add, add_assoc]

theorem affineActionHom_injective : Function.Injective (affineActionHom F d) := by
  intro g h he
  have ht := congrArg (fun p : Equiv.Perm (Fin d → F) => p 0) he
  change g.left.toAdd + matrixLinearEquiv F d g.right 0 =
    h.left.toAdd + matrixLinearEquiv F d h.right 0 at ht
  simp only [map_zero, add_zero] at ht
  have hl : g.left = h.left := congrArg Multiplicative.ofAdd ht
  have hr : matrixLinearEquiv F d g.right = matrixLinearEquiv F d h.right := by
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun p : Equiv.Perm (Fin d → F) => p v) he
    change g.left.toAdd + matrixLinearEquiv F d g.right v =
      h.left.toAdd + matrixLinearEquiv F d h.right v at hv
    rw [ht] at hv
    exact add_left_cancel hv
  exact SemidirectProduct.ext hl ((matrixLinearEquiv F d).injective hr)

noncomputable def affineImage : Subgroup (Equiv.Perm (Fin d → F)) :=
  (affineActionHom F d).range

variable {F d}

/-- One explicit coefficient suffices for the already-proved affine
valuation constant. This is numerical absorption, with no group premise. -/
theorem affine_coefficient_absorption {C : ℝ} (hC : 512 ≤ C) {n : ℕ} (hn : 3 ≤ n) :
    (12 / Real.log 2) * Real.log n ≤ degreeAllowance C n := by
  rw [allowance_large C hn]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (12 / Real.log 2 : ℝ) ≤ 18 := by
    apply (div_le_iff₀ hlog2).mpr
    have h := Johnson.log_two_lower
    linarith
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : (1579 / 1500 : ℝ) ≤ Real.log n :=
    Johnson.log_three_lower.le.trans (Real.log_le_log (by norm_num) hnR)
  have hprod := mul_le_mul (show (494 : ℝ) ≤ C - 18 by linarith)
    (show (79 / 1500 : ℝ) ≤ Real.log n - 1 by linarith)
    (by norm_num : (0 : ℝ) ≤ 79 / 1500) (by linarith : 0 ≤ C - 18)
  have hfirst := mul_le_mul_of_nonneg_right hA (show 0 ≤ Real.log n by linarith)
  nlinarith

/-- Every actual permutation image of an affine group, and every subgroup
of that image, satisfies A.9 at the vector-space degree. -/
theorem sigma_affine_image {V : Type*} [Fintype V] [Fintype F]
    {cutoff : ℕ} {C : ℝ} (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C)
    (p : AffineGroup F d →* Equiv.Perm V)
    (hdegree : Fintype.card V = (Fintype.card F) ^ d)
    (H : Subgroup (Equiv.Perm V)) (hH : H ≤ p.range) (a : V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  by_cases hn : Fintype.card V ≤ 2
  · exact sigma_small_degree (by omega) (by linarith) (by omega) H a
  obtain ⟨q, hq, hv⟩ := affine_subgroup_uniform_bound F d ⊤
  have hc : Nat.card (⊤ : Subgroup (AffineGroup F d)) = Nat.card (AffineGroup F d) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hc] at hv
  haveI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
  have hdvd := (Subgroup.card_dvd_of_le hH).trans (Subgroup.card_range_dvd p)
  have hm := primeValuation_mono (p := q)
    (Nat.ne_of_gt (Nat.card_pos (α := AffineGroup F d))) hdvd
  have hs := sigma_valuation_bound hq hcutoff a H
  have hsr : (sigma cutoff a H : ℝ) ≤ 6 * (padicValNat q (Nat.card H) : ℝ) := by
    exact_mod_cast hs
  have hmr : (padicValNat q (Nat.card H) : ℝ) ≤
      padicValNat q (Nat.card (AffineGroup F d)) := by exact_mod_cast hm
  have hv' : 6 * (padicValNat q (Nat.card (AffineGroup F d)) : ℝ) ≤
      (12 / Real.log 2) * Real.log (Fintype.card V) := by
    simpa only [hdegree, Nat.cast_pow] using hv
  exact (hsr.trans ((mul_le_mul_of_nonneg_left hmr (by norm_num)).trans hv')).trans
    (affine_coefficient_absorption hC (by omega))

/-- The concrete natural affine case requires no recognition or abstract
representation hypothesis: its full faithful action was constructed above. -/
theorem sigma_natural_affine [Fintype F] {cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 512 ≤ C)
    (H : Subgroup (Equiv.Perm (Fin d → F))) (hH : H ≤ affineImage F d) (v : Fin d → F) :
    (sigma cutoff v H : ℝ) ≤ degreeAllowance C (Fintype.card (Fin d → F)) :=
  sigma_affine_image hcutoff hC (affineActionHom F d)
    (by simp only [Fintype.card_fun, Fintype.card_fin]) H hH v

end GI.BudgetInduction
