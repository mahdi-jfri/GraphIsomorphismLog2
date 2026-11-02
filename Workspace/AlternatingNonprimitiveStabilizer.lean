import Workspace.NaturalCoordinatesGiant
import Workspace.AlternatingImprimitiveBudget

namespace GI.BudgetInduction

/-- Under an explicit natural alternating realization, all nonprimitive
natural-stabilizer cases now give an actual primitive reduction. The
intransitive case constructs Johnson coordinates; the transitive
imprimitive case proves the exponential-index valuation estimate. -/
theorem primitive_alternative_of_nonprimitive_natural_stabilizer {m n : ℕ} {A₀ : ℝ}
    (G : Subgroup (Equiv.Perm (Fin m))) [MulAction G (Fin n)]
    [MulAction.IsPreprimitive G (Fin n)] [Nontrivial (Fin n)]
    (giant : alternatingGroup (Fin m) ≤ G) (hdegree : 3 ≤ m) (v : Fin n)
    (nongiant : ¬ alternatingGroup (Fin n) ≤ (MulAction.toPermHom G (Fin n)).range)
    (nonprimitive : ¬ MulAction.IsPreprimitive
      ((MulAction.stabilizer G v).map G.subtype) (Fin m))
    (hA : 24 / Real.log 2 ≤ A₀) :
    PrimitiveReductionAlternative A₀ (MulAction.toPermHom G (Fin n)).range := by
  classical
  by_cases ht : MulAction.IsPretransitive ((MulAction.stabilizer G v).map G.subtype) (Fin m)
  · letI := ht
    exact primitive_alternative_of_imprimitive_natural_stabilizer G giant v
      ⟨0, by omega⟩ nonprimitive hA
  · exact primitive_alternative_of_intransitive_natural_stabilizer G giant hdegree v nongiant ht

end GI.BudgetInduction
