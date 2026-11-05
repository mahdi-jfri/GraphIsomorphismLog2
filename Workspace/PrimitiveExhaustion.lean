module

public import Workspace.PrimitiveValuationCases
public import Workspace.BudgetInductionRadicalFree
public import Workspace.UnsupportedSocleAlternative

@[expose] public section

/-!
# Primitive exhaustion and the hereditary budget (Theorem A.9)

The proof of Theorem A.9 uses strong induction on the permutation degree `n` and,
for a fixed degree `n`, strong induction on the group order `|H|`. The structural
reduction (O'Nan–Scott in the form proved by the library, without CFSG) is:
* an intransitive group reduces to its active orbit of smaller degree;
* a transitive imprimitive group decomposes into block-label and within-block
  actions of smaller degrees;
* a primitive group with a nontrivial solvable radical gives the affine case;
* otherwise the group has trivial solvable radical, and either a proper-projection
  product action gives a Cartesian cover, or `|socle(H)| ≤ n²` (the regular,
  diagonal, and twisted-wreath cases, bounded via `socle_sigma_bound` and
  `GI.schreier`), or `socle(H)` is a nonabelian simple group, where no marked
  step occurs at `H` (`no_almostSimple_step` from `GI.schreier`) and any marked
  chain first restricts to a proper subgroup `L < H` of smaller order `|L| < |H|`.
-/

namespace GI.PrimitiveValuation

open RadicalSocle BudgetInduction

/-- The constant `A₀` of Lemma A.8. -/
noncomputable def primitiveConstant : ℝ :=
  max (max (12 / Real.log 2) alternatingConstant) (max diagonalBudgetConstant 0)

theorem primitiveConstant_nonneg : 0 ≤ primitiveConstant :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The socle of a radical-free group is nonabelian, when the group is nontrivial. -/
theorem socle_nonabelian {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (radicalFree : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) :
    ∃ x y : socle G, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  have hbot := radicalFree (socle G) inferInstance (Group.isSolvable_of_comm hc)
  obtain ⟨N, hN, _⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  exact hN.2.1 (le_bot_iff.mp (hbot ▸ minimalNormal_le_socle hN))

/-- Theorem A.9 for permutation groups on `Fin n`, with `C` independent of the
cutoff `kcert ≥ 64`. -/
theorem hereditary_budget_fin :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ cutoff : ℕ, 64 ≤ cutoff →
      ∀ n : ℕ, ∀ H : Subgroup (Equiv.Perm (Fin n)), ∀ a : Fin n,
        (sigma cutoff a H : ℝ) ≤ degreeAllowance C n := by
  obtain ⟨C, hC, absorb⟩ :=
    exists_coefficient_for_primitive_reduction primitiveConstant primitiveConstant_nonneg
  refine ⟨C, hC, ?_⟩
  intro cutoff hcutoff n
  have hfive : 5 ≤ cutoff := by omega
  induction n using Nat.strong_induction_on with
  | h n ih_deg =>
    have ih_top : ∀ m < n, ∀ b : Fin m, (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m :=
      fun m hm b => ih_deg m hm ⊤ b
    suffices hord : ∀ ord : ℕ, ∀ H : Subgroup (Equiv.Perm (Fin n)), Nat.card H = ord →
        ∀ a : Fin n, (sigma cutoff a H : ℝ) ≤ degreeAllowance C n by
      intro H a
      exact hord (Nat.card H) H rfl a
    intro ord
    induction ord using Nat.strong_induction_on with
    | h ord ih_ord =>
      intro H hcardH a
      by_cases hn : n < cutoff
      · simpa only [Fintype.card_fin] using
          sigma_small_degree hfive hC (V := Fin n) (by simpa only [Fintype.card_fin] using hn) H a
      have hn3 : 3 ≤ n := by omega
      have hn2 : 2 ≤ Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
      by_cases ht : MulAction.IsPretransitive H (Fin n)
      · letI := ht
        by_cases hp : MulAction.IsPreprimitive H (Fin n)
        · letI := hp
          by_cases halt : PrimitiveReductionAlternative primitiveConstant H
          · exact sigma_of_primitive_alternative hcutoff hC hn3 absorb ih_top H a halt
          · have h12 : 12 / Real.log 2 ≤ primitiveConstant :=
              (le_max_left _ _).trans (le_max_left _ _)
            have hdiag : diagonalBudgetConstant ≤ primitiveConstant :=
              (le_max_left _ _).trans (le_max_right _ _)
            have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
            have hrad : solvableRadical H = ⊥ := by
              by_contra hne
              exact halt (primitive_alternative_of_nontrivial_solvable_radical H a hne h12)
            have radicalFree : ∀ K : Subgroup H, K.Normal → Group.IsSolvable K → K = ⊥ := by
              intro K hK hs
              have := hK
              have : Group.IsSolvable K := hs
              exact le_bot_iff.mp (hrad ▸ le_solvableRadical K)
            have : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp hn2
            rcases unsupported_socle_simple_or_order_le_degree_sq H radicalFree a halt with hs | hb
            · have : Nontrivial H := by
                obtain ⟨b, hb⟩ := exists_ne a
                obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a b
                refine ⟨⟨g, 1, fun he => ?_⟩⟩
                rw [he, one_smul] at hg
                exact hb hg.symm
              have hna := socle_nonabelian radicalFree
              have hno : ∀ (L : Subgroup (Equiv.Perm (Fin n))) (k : ℕ),
                  cutoff ≤ k → VisibleStep a H L k → False :=
                fun L k hk s => HbudAlmostSimple.no_almostSimple_step hn2 hs hna (hfive.trans hk) s
              rcases HbudAlmostSimple.sigma_eq_zero_or_proper_subgroup hfive a H hno with
                hz | ⟨L, hlt, hle⟩
              · rw [hz, Nat.cast_zero]
                exact allowance_nonneg hC n
              · have hlt_card : Nat.card L < ord := by
                  rw [← hcardH]
                  by_contra hn_lt
                  exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (Nat.le_of_not_gt hn_lt))
                exact (Nat.cast_le.mpr hle).trans (ih_ord (Nat.card L) hlt_card L rfl a)
            · exact (socle_sigma_bound radicalFree hb hcutoff a).trans
                ((mul_le_mul_of_nonneg_right hdiag hlogn).trans (absorb n hn3))
        · simpa only [Fintype.card_fin] using
            sigma_imprimitive hfive hC (V := Fin n) (by simpa only [Fintype.card_fin] using ih_top)
              H a hp
      · simpa only [Fintype.card_fin] using
          sigma_intransitive hfive hC (V := Fin n) (by simpa only [Fintype.card_fin] using ih_top)
            H a ht

/-- Theorem A.9 for permutation groups on an arbitrary finite set. -/
theorem hereditary_budget :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ cutoff : ℕ, 64 ≤ cutoff →
      ∀ (Ω : Type*) [Fintype Ω], ∀ G : Subgroup (Equiv.Perm Ω), ∀ α : Ω,
        (sigma cutoff α G : ℝ) ≤ degreeAllowance C (Fintype.card Ω) := by
  obtain ⟨C, hC, h⟩ := hereditary_budget_fin
  refine ⟨C, hC, ?_⟩
  intro cutoff hcutoff Ω _ G α
  let e := Fintype.equivFin Ω
  rw [sigma_relabel cutoff e G α]
  exact h cutoff hcutoff _ _ _

end GI.PrimitiveValuation
