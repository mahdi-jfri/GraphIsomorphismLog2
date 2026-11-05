module

public import Workspace.PhysicalActionTransport
public import Workspace.BoundedSocleValuation
public import Workspace.AlternatingSocleEmbedding
public import Workspace.AlternatingNaturalRealization

@[expose] public section

namespace GI.BudgetInduction

/-- The alternating-socle action model is constructed from the actual
socle and its actual isomorphism. The physical action is transported
through the resulting group equivalence with exactly the original image. -/
theorem primitive_alternative_of_large_alternating_socle {n m : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (e : RadicalSocle.socle H ≃* alternatingGroup (Fin m))
    (hm : 7 ≤ m) (hn : 3 ≤ n) (v : Fin n)
    (nongiant : ¬ alternatingGroup (Fin n) ≤ H)
    (hA : 24 / Real.log 2 ≤ A₀) : PrimitiveReductionAlternative A₀ H := by
  let hdegree : Fintype.card (Fin m) = 5 ∨ 7 ≤ Fintype.card (Fin m) :=
    Or.inr (by simpa only [Fintype.card_fin] using hm)
  let K := (AlternatingSocle.naturalHom e hdegree).range
  let E : H ≃* K := AlternatingSocle.naturalEquiv radicalFree e hdegree
  letI : MulAction K (Fin n) := PhysicalTransport.action E
  letI : MulAction.IsPreprimitive K (Fin n) := PhysicalTransport.preprimitive E
  have hold : (MulAction.toPermHom H (Fin n)).range = H := by
    change H.subtype.range = H
    exact Subgroup.range_subtype H
  have himage : (MulAction.toPermHom K (Fin n)).range = H :=
    (PhysicalTransport.image_eq E).trans hold
  have giant : alternatingGroup (Fin m) ≤ K := AlternatingSocle.alternating_le_natural_range e hdegree
  have hb := primitive_alternative_of_natural_alternating_realization K giant (by omega) hn v
    (by rw [himage]; exact nongiant) hA
  rwa [himage] at hb

/-- All actual alternating-socle primitive nongiant cases meet the
primitive alternatives. Large degrees use the proved automorphism model;
bounded degrees, including six, use the direct finite socle bound. -/
theorem primitive_alternative_of_alternating_socle {n m : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (e : RadicalSocle.socle H ≃* alternatingGroup (Fin m))
    (hn : 3 ≤ n) (v : Fin n) (nongiant : ¬ alternatingGroup (Fin n) ≤ H)
    (hA : max (24 / Real.log 2) (2160 / Real.log 3) ≤ A₀) :
    PrimitiveReductionAlternative A₀ H := by
  by_cases hm : m ≤ 6
  · exact primitive_alternative_of_small_alternating_socle H radicalFree e hm hn
      ((le_max_right _ _).trans hA)
  · exact primitive_alternative_of_large_alternating_socle H radicalFree e (by omega) hn v nongiant
      ((le_max_left _ _).trans hA)

/-- Any remaining unsupported actual primitive nongiant action has no
alternating-group isomorphism of its socle, in any natural degree. -/
theorem unsupported_socle_not_alternating {n : ℕ} {A₀ : ℝ}
    (H : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive H (Fin n)]
    (radicalFree : ∀ N : Subgroup H, N.Normal → IsSolvable N → N = ⊥)
    (hn : 3 ≤ n) (v : Fin n) (nongiant : ¬ alternatingGroup (Fin n) ≤ H)
    (hA : max (24 / Real.log 2) (2160 / Real.log 3) ≤ A₀)
    (unsupported : ¬ PrimitiveReductionAlternative A₀ H) :
    ∀ m : ℕ, ¬ Nonempty (RadicalSocle.socle H ≃* alternatingGroup (Fin m)) := by
  rintro m ⟨e⟩
  exact unsupported (primitive_alternative_of_alternating_socle H radicalFree e hn v nongiant hA)

end GI.BudgetInduction
