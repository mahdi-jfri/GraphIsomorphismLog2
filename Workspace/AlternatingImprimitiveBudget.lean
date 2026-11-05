module

public import Workspace.AlternatingImprimitiveDegree
public import Workspace.BudgetInductionAlternatives

@[expose] public section

namespace GI.AlternatingActions

variable {A V : Type*} [Fintype A] (G : Subgroup (Equiv.Perm A)) [MulAction G V]

/-- The actual physical permutation image has three-adic charge at most
three times the explicit natural degree, by Lagrange and Legendre. -/
theorem physical_image_three_valuation_le :
    6 * padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) ≤ 3 * Nat.card A := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd : Nat.card (MulAction.toPermHom G V).range ∣ (Nat.card A).factorial := by
    rw [← Nat.card_perm]
    exact (Subgroup.card_range_dvd (MulAction.toPermHom G V)).trans G.card_subgroup_dvd_card
  have hv := GI.primeValuation_mono (p := 3) (Nat.factorial_ne_zero _) hd
  have hleg := sub_one_mul_padicValNat_factorial (p := 3) (Nat.card A)
  have hsub := Nat.sub_le (Nat.card A) ((3 : ℕ).digits (Nat.card A)).sum
  norm_num only at hleg
  omega

variable [DecidableEq A] [Fintype V] [Nontrivial V] [MulAction.IsPretransitive G V]

/-- The imprimitive-stabilizer branch meets the actual order-valuation
alternative with an explicit uniform logarithmic constant. -/
theorem imprimitive_stabilizer_valuation_log_bound
    (giant : alternatingGroup A ≤ G) (v : V) (x : A)
    [MulAction.IsPretransitive ((MulAction.stabilizer G v).map G.subtype) A]
    (imprimitive : ¬ MulAction.IsPreprimitive
      ((MulAction.stabilizer G v).map G.subtype) A) :
    6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
      (24 / Real.log 2) * Real.log (Nat.card V : ℝ) := by
  have hv : 6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
      3 * (Nat.card A : ℝ) := by exact_mod_cast physical_image_three_valuation_le G
  have hd := imprimitive_stabilizer_natural_degree_log_bound G giant v x imprimitive
  calc
    6 * (padicValNat 3 (Nat.card (MulAction.toPermHom G V).range) : ℝ) ≤
        3 * (Nat.card A : ℝ) := hv
    _ ≤ 3 * ((8 / Real.log 2) * Real.log (Nat.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = (24 / Real.log 2) * Real.log (Nat.card V : ℝ) := by ring

end GI.AlternatingActions

namespace GI.BudgetInduction

/-- A direct adapter into the primitive-reduction predicate for the
actual physical image of an explicitly realized natural alternating
overgroup. No automorphism classification is a premise or conclusion. -/
theorem primitive_alternative_of_imprimitive_natural_stabilizer {m n : ℕ} {A₀ : ℝ}
    (G : Subgroup (Equiv.Perm (Fin m))) [MulAction G (Fin n)]
    [MulAction.IsPretransitive G (Fin n)] [Nontrivial (Fin n)]
    (giant : alternatingGroup (Fin m) ≤ G) (v : Fin n) (x : Fin m)
    [MulAction.IsPretransitive ((MulAction.stabilizer G v).map G.subtype) (Fin m)]
    (imprimitive : ¬ MulAction.IsPreprimitive
      ((MulAction.stabilizer G v).map G.subtype) (Fin m))
    (hA : 24 / Real.log 2 ≤ A₀) :
    PrimitiveReductionAlternative A₀ (MulAction.toPermHom G (Fin n)).range := by
  have hb := AlternatingActions.imprimitive_stabilizer_valuation_log_bound G giant v x imprimitive
  have hcard : Nat.card (Fin n) = n := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hcard] at hb
  have hn : 1 < n := by simpa using (Fintype.one_lt_card (α := Fin n))
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  exact Or.inl ⟨3, Or.inl rfl, hb.trans (mul_le_mul_of_nonneg_right hA hlog)⟩

end GI.BudgetInduction
