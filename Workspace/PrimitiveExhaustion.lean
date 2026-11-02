import Workspace.PrimitiveValuationCases
import Workspace.BudgetInductionRadicalFree
import Workspace.UnsupportedSocleAlternative

/-!
# Primitive exhaustion and the hereditary budget (Theorem A.9)

The proof of Theorem A.9 needs: every primitive nongiant group meets one of the
three reductions of `PrimitiveReductionAlternative` (a valuation bound from
Lemma A.8, a Cartesian product action, or a Johnson action). The structural
reduction (O'Nan-Scott in the form proved by the library, without CFSG) is:
* a nontrivial solvable radical gives the affine case;
* otherwise the socle is simple, or its order is at most `n^2` (product actions
  with proper projections give a Cartesian cover; the remaining diagonal,
  twisted and two-regular-normal cases have `|socle| ≤ n^2`, the inequality
  `n ≥ |T|^{s/2}` of `eq:budget-diagonal-degree`);
* a simple socle is alternating or not.
Each terminal case is one of the cases of Lemma A.8.
-/

namespace GI.PrimitiveValuation

open RadicalSocle BudgetInduction

/-- The constant `A₀` of Lemma A.8, given the constant `A` of the cited
Lie-type estimate. -/
noncomputable def primitiveConstant (A : ℝ) : ℝ :=
  max (max (12 / Real.log 2) alternatingConstant)
    (max WreathValuation.diagonalConstant (max A 0))

theorem primitiveConstant_nonneg (A : ℝ) : 0 ≤ primitiveConstant A :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The socle of a radical-free group is nonabelian, when the group is nontrivial. -/
theorem socle_nonabelian {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (radicalFree : ∀ R : Subgroup G, R.Normal → IsSolvable R → R = ⊥) :
    ∃ x y : socle G, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  haveI : IsSolvable (socle G) := isSolvable_of_comm hc
  have hbot := radicalFree (socle G) inferInstance inferInstance
  obtain ⟨N, hN, _⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  exact hN.2.1 (le_bot_iff.mp (hbot ▸ minimalNormal_le_socle hN))

/-- **Primitive exhaustion.** With the two cited inputs, there is one constant
`A₀` such that every primitive group of degree `n ≥ 3` not containing `Alt(n)`
satisfies one of the primitive reductions used in Theorem A.9. -/
theorem primitive_exhaustion (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ n : ℕ, 3 ≤ n → ∀ H : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPreprimitive H (Fin n) → ¬ alternatingGroup (Fin n) ≤ H →
      PrimitiveReductionAlternative A₀ H := by
  obtain ⟨A, hA⟩ := almostSimple_valuation hLie
  refine ⟨primitiveConstant A, primitiveConstant_nonneg A, ?_⟩
  intro n hn H hp hng
  letI := hp
  have h12 : 12 / Real.log 2 ≤ primitiveConstant A :=
    (le_max_left _ _).trans (le_max_left _ _)
  have halt : max (24 / Real.log 2) (2160 / Real.log 3) ≤ primitiveConstant A :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hdiag : WreathValuation.diagonalConstant ≤ primitiveConstant A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hlie : A ≤ primitiveConstant A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  let a : Fin n := ⟨0, by omega⟩
  haveI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Fintype.card_fin] using (show 1 < n by omega))
  by_contra hun
  by_cases hrad : solvableRadical H = ⊥
  · have radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥ := by
      intro K hK hs
      haveI := hK
      haveI := hs
      exact le_bot_iff.mp (hrad ▸ le_solvableRadical K)
    rcases unsupported_socle_simple_or_order_le_degree_sq H radicalFree a hun with hs | hb
    · haveI : Nontrivial H := by
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a ⟨1, by omega⟩
        refine ⟨⟨g, 1, fun he => ?_⟩⟩
        rw [he, one_smul] at hg
        exact absurd (congrArg Fin.val hg) (by simp [a])
      have hna := socle_nonabelian radicalFree
      by_cases hal : ∃ m : ℕ, Nonempty (socle H ≃* alternatingGroup (Fin m))
      · obtain ⟨m, ⟨e⟩⟩ := hal
        exact hun (primitive_alternative_of_alternating_socle H radicalFree e hn a hng halt)
      · push Not at hal
        obtain ⟨ℓ, hℓ, hv⟩ := hA n H hs hna hal
        exact hun (Or.inl ⟨ℓ, hℓ, hv.trans (mul_le_mul_of_nonneg_right hlie hlogn)⟩)
    · exact hun (Or.inl ⟨3, Or.inl rfl, (socle_valuation hAut radicalFree hb).trans
        (mul_le_mul_of_nonneg_right hdiag hlogn)⟩)
  · exact hun (primitive_alternative_of_nontrivial_solvable_radical H a hrad h12)

/-- Theorem A.9 for permutation groups on `Fin n`, with `C` independent of the
cutoff `kcert ≥ 64`. -/
theorem hereditary_budget_fin (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ cutoff : ℕ, 64 ≤ cutoff →
      ∀ n : ℕ, ∀ H : Subgroup (Equiv.Perm (Fin n)), ∀ a : Fin n,
        (sigma cutoff a H : ℝ) ≤ degreeAllowance C n := by
  obtain ⟨A₀, hA₀, hex⟩ := primitive_exhaustion hAut hLie
  obtain ⟨C, hC, absorb⟩ := exists_coefficient_for_primitive_reduction A₀ hA₀
  refine ⟨C, hC, ?_⟩
  intro cutoff hcutoff n H a
  have hnat := natural_bound_of_primitive_exhaustion hcutoff hC absorb
    (fun n hn H hp hng => hex n (by omega) H hp hng)
  exact (Nat.cast_le.mpr (sigma_subgroup_mono (by omega) a le_top)).trans (hnat n a)

/-- Theorem A.9 for permutation groups on an arbitrary finite set. -/
theorem hereditary_budget (hAut : GI.Cited.AutCardLeSq)
    (hLie : GI.Cited.SimpleValuationDegree) :
    ∃ C : ℝ, 128 ≤ C ∧ ∀ cutoff : ℕ, 64 ≤ cutoff →
      ∀ (Ω : Type*) [Fintype Ω], ∀ G : Subgroup (Equiv.Perm Ω), ∀ α : Ω,
        (sigma cutoff α G : ℝ) ≤ degreeAllowance C (Fintype.card Ω) := by
  obtain ⟨C, hC, h⟩ := hereditary_budget_fin hAut hLie
  refine ⟨C, hC, ?_⟩
  intro cutoff hcutoff Ω _ G α
  let e := Fintype.equivFin Ω
  rw [sigma_relabel cutoff e G α]
  exact h cutoff hcutoff _ _ _

end GI.PrimitiveValuation
