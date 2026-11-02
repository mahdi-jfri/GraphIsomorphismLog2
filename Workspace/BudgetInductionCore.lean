import Workspace.BudgetInductionBlocks

namespace GI.BudgetInduction

/-- With all smaller natural degrees bounded, an offending natural action
produces a same-degree primitive nongiant offender. This is an unconditional
reduction of counterexamples, not a primitive-classification assumption. -/
theorem primitive_witness_of_minimal_failure {cutoff n : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (ih : ∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    (a : Fin n) (hfail : degreeAllowance C n < (sigma cutoff a ⊤ : ℝ)) :
    cutoff ≤ n ∧ ∃ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) ∧ ¬ alternatingGroup (Fin n) ≤ H ∧
      degreeAllowance C n < (sigma cutoff a H : ℝ) := by
  classical
  have hfive : 5 ≤ cutoff := by omega
  have hn : cutoff ≤ n := by
    by_contra hn
    have hz := sigma_small_degree hfive hC (V := Fin n)
      (by simpa only [Fintype.card_fin] using (show n < cutoff by omega)) ⊤ a
    rw [Fintype.card_fin] at hz
    exact not_lt_of_ge hz hfail
  obtain ⟨H, hH, hng, heq⟩ := NaturalGiant.exists_nongiant_same_sigma_fin hfive
    (by omega) a ⊤ le_top
  have hfailH : degreeAllowance C n < (sigma cutoff a H : ℝ) := by rwa [heq]
  have ht : MulAction.IsPretransitive H (Fin n) := Classical.byContradiction fun hnt => by
    have hh := sigma_intransitive hfive hC (V := Fin n)
      (by simpa only [Fintype.card_fin] using ih) H a hnt
    exact not_lt_of_ge (by simpa only [Fintype.card_fin] using hh) hfailH
  letI := ht
  have hp : MulAction.IsPreprimitive H (Fin n) := Classical.byContradiction fun hnp => by
    have hh := sigma_imprimitive hfive hC (V := Fin n)
      (by simpa only [Fintype.card_fin] using ih) H a hnp
    exact not_lt_of_ge (by simpa only [Fintype.card_fin] using hh) hfailH
  exact ⟨hn, H, hp, hng, hfailH⟩

/-- Strong induction closes every intransitive, imprimitive and natural-giant
case. The displayed primitive step is precisely the remaining obligation;
this theorem is a reduction and is not asserted as completed Appendix A.9. -/
theorem natural_bound_of_primitive_steps {cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (primitive : ∀ n, cutoff ≤ n →
      (∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m) →
      ∀ (H : Subgroup (Equiv.Perm (Fin n))),
        MulAction.IsPreprimitive H (Fin n) → ¬ alternatingGroup (Fin n) ≤ H →
        ∀ a : Fin n, (sigma cutoff a H : ℝ) ≤ degreeAllowance C n) :
    ∀ n, ∀ a : Fin n, (sigma cutoff a ⊤ : ℝ) ≤ degreeAllowance C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a
      by_contra hn
      have hfail := lt_of_not_ge hn
      obtain ⟨hn, H, hp, hng, hh⟩ :=
        primitive_witness_of_minimal_failure hcutoff hC ih a hfail
      exact not_lt_of_ge (primitive n hn ih H hp hng a) hh

/-- Any failure anywhere has a least-degree primitive nongiant witness,
with the exact smaller-degree induction hypotheses available. No structural
classification theorem is assumed here. -/
theorem primitive_witness_of_failure {cutoff : ℕ} {C : ℝ}
    (hcutoff : 64 ≤ cutoff) (hC : 128 ≤ C)
    (failure : ∃ n, ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a ⊤ : ℝ)) :
    ∃ n, cutoff ≤ n ∧
      (∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m) ∧
      ∃ H : Subgroup (Equiv.Perm (Fin n)),
        MulAction.IsPreprimitive H (Fin n) ∧ ¬ alternatingGroup (Fin n) ≤ H ∧
        ∃ a : Fin n, degreeAllowance C n < (sigma cutoff a H : ℝ) := by
  classical
  let n := Nat.find failure
  obtain ⟨a, ha⟩ := Nat.find_spec failure
  have ih : ∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m := by
    intro m hm b
    by_contra hb
    exact Nat.find_min failure hm ⟨b, lt_of_not_ge hb⟩
  obtain ⟨hn, H, hp, hng, hh⟩ := primitive_witness_of_minimal_failure hcutoff hC ih a ha
  exact ⟨n, hn, ih, H, hp, hng, a, hh⟩

end GI.BudgetInduction
