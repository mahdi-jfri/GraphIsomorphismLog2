module

public import Workspace.SmallDegreeBudget
public import Workspace.NaturalGiantMarks
public import Workspace.JohnsonNumerics
public import Mathlib.GroupTheory.GroupAction.Primitive

@[expose] public section

namespace GI.BudgetInduction

/-- The exact piecewise right-hand side of Appendix A.9. -/
noncomputable def degreeAllowance (C : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 2 then 0 else C * Real.log n - (C + 6)

theorem allowance_small (C : ℝ) {n : ℕ} (hn : n ≤ 2) :
    degreeAllowance C n = 0 := if_pos hn

theorem allowance_large (C : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    degreeAllowance C n = C * Real.log n - (C + 6) := if_neg (by omega)

theorem allowance_nonneg {C : ℝ} (hC : 128 ≤ C) (n : ℕ) :
    0 ≤ degreeAllowance C n := by
  by_cases hn : n ≤ 2
  · rw [allowance_small C hn]
  · rw [allowance_large C (by omega)]
    exact (Johnson.fresh_budget_pos hC (by exact_mod_cast (show 3 ≤ n by omega))).le

theorem allowance_mono {C : ℝ} (hC : 128 ≤ C) {m n : ℕ} (hmn : m ≤ n) :
    degreeAllowance C m ≤ degreeAllowance C n := by
  by_cases hm : m ≤ 2
  · rw [allowance_small C hm]
    exact allowance_nonneg hC n
  · have hm3 : 3 ≤ m := by omega
    rw [allowance_large C hm3, allowance_large C (hm3.trans hmn)]
    have hl : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast hmn)
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hl (by linarith)) _

/-- The two block dimensions pay only one shifted logarithmic bound. The
degree-two cases use the actual zero convention. -/
theorem allowance_mul {C : ℝ} (hC : 128 ≤ C) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    degreeAllowance C a + degreeAllowance C b ≤ degreeAllowance C (a * b) := by
  have ham : a ≤ a * b := Nat.le_mul_of_pos_right a (by omega)
  have hbm : b ≤ a * b := Nat.le_mul_of_pos_left b (by omega)
  by_cases ha2 : a ≤ 2
  · rw [allowance_small C ha2, zero_add]
    exact allowance_mono hC hbm
  by_cases hb2 : b ≤ 2
  · rw [allowance_small C hb2, add_zero]
    exact allowance_mono hC ham
  have ha3 : 3 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  rw [allowance_large C ha3, allowance_large C hb3,
    allowance_large C (ha3.trans ham), Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (show a ≠ 0 by omega))
      (by exact_mod_cast (show b ≠ 0 by omega))]
  nlinarith

variable {V : Type*} [Fintype V]

/-- Relabeling and subgroup monotonicity turn the natural symmetric bound
at one degree into the bound for every action at that degree. -/
theorem sigma_le_of_natural {cutoff : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (hn : ∀ a : Fin (Fintype.card V),
      (sigma cutoff a ⊤ : ℝ) ≤ degreeAllowance C (Fintype.card V))
    (H : Subgroup (Equiv.Perm V)) (a : V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  classical
  let e := Fintype.equivFin V
  rw [sigma_relabel cutoff e H a]
  exact (Nat.cast_le.mpr (sigma_subgroup_mono hcutoff (e a) le_top)).trans (hn (e a))

theorem sigma_le_of_smaller_degree {cutoff n : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (ih : ∀ m < n, ∀ a : Fin m, (sigma cutoff a ⊤ : ℝ) ≤ degreeAllowance C m)
    (hcard : Fintype.card V < n) (H : Subgroup (Equiv.Perm V)) (a : V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) :=
  sigma_le_of_natural hcutoff (ih _ hcard) H a

theorem sigma_small_degree {cutoff : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (hC : 128 ≤ C) (hcard : Fintype.card V < cutoff)
    (H : Subgroup (Equiv.Perm V)) (a : V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  rw [sigma_zero_of_degree hcutoff hcard H a, Nat.cast_zero]
  exact allowance_nonneg hC _

theorem orbit_card_le (H : Subgroup (Equiv.Perm V)) (a : V)
    [Fintype (ActiveOrbit H a)] : Fintype.card (ActiveOrbit H a) ≤ Fintype.card V :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- Intransitivity makes every active orbit strictly smaller than the
physical permutation domain. -/
theorem orbit_card_lt_of_not_pretransitive (H : Subgroup (Equiv.Perm V)) (a : V)
    [Fintype (ActiveOrbit H a)] (hn : ¬ MulAction.IsPretransitive H V) :
    Fintype.card (ActiveOrbit H a) < Fintype.card V := by
  apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
  intro hs
  apply hn
  apply (MulAction.isPretransitive_iff_orbit_eq_univ a).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, rfl⟩ := hs x
  exact y.property

/-- The intransitive induction case uses the actual faithful orbit image;
all its representation and degree changes are proved. -/
theorem sigma_intransitive {cutoff : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (hC : 128 ≤ C)
    (ih : ∀ m < Fintype.card V, ∀ b : Fin m,
      (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    (H : Subgroup (Equiv.Perm V)) (a : V)
    (hn : ¬ MulAction.IsPretransitive H V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  classical
  letI : Fintype (ActiveOrbit H a) := Fintype.ofFinite _
  rw [sigma_faithfulOrbit cutoff H a]
  exact (sigma_le_of_smaller_degree hcutoff ih
    (orbit_card_lt_of_not_pretransitive H a hn) (faithfulOrbitImage H a)
    (activeOrbitBase H a)).trans (allowance_mono hC (orbit_card_le H a))

end GI.BudgetInduction
