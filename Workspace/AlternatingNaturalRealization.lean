import Workspace.AlternatingNonprimitiveStabilizer
import Workspace.AlternatingPrimitiveStabilizer

namespace GI.BudgetInduction

/-- Every physical nongiant primitive action of an explicitly realized
natural alternating overgroup satisfies the actual primitive alternatives.
The three cases are derived from the natural action of its actual physical
point stabilizer. No alternating automorphism realization is asserted. -/
theorem primitive_alternative_of_natural_alternating_realization {m n : ℕ} {A₀ : ℝ}
    (G : Subgroup (Equiv.Perm (Fin m))) [MulAction G (Fin n)]
    [MulAction.IsPreprimitive G (Fin n)]
    (giant : alternatingGroup (Fin m) ≤ G) (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Fin n)
    (nongiant : ¬ alternatingGroup (Fin n) ≤ (MulAction.toPermHom G (Fin n)).range)
    (hA : 24 / Real.log 2 ≤ A₀) :
    PrimitiveReductionAlternative A₀ (MulAction.toPermHom G (Fin n)).range := by
  classical
  haveI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Fintype.card_fin] using (show 1 < n by omega))
  by_cases hp : MulAction.IsPreprimitive ((MulAction.stabilizer G v).map G.subtype) (Fin m)
  · apply primitive_alternative_of_primitive_natural_stabilizer G giant hm hn v hp
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact (div_le_div_of_nonneg_right (by norm_num : (18 : ℝ) ≤ 24) hlog.le).trans hA
  · exact primitive_alternative_of_nonprimitive_natural_stabilizer G giant hm v nongiant hp hA

end GI.BudgetInduction
