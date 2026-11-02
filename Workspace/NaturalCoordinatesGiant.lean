import Workspace.AlternatingNaturalJohnson
import Workspace.BudgetInductionAlternatives

namespace GI.AlternatingActions

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
  (G : Subgroup (Equiv.Perm A)) [MulAction G V]

/-- Natural equivariant coordinates transport the actual alternating
subgroup into the physical image, using invariance of permutation sign. -/
theorem natural_coordinates_giant (giant : alternatingGroup A ≤ G) (e : V ≃ A)
    (equivariant : ∀ (g : G) (v : V), e (g • v) = (g : Equiv.Perm A) (e v)) :
    alternatingGroup V ≤ (MulAction.toPermHom G V).range := by
  intro p hp
  have hq : GI.relabelPerm e p ∈ alternatingGroup A := by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (e.permCongr p) = 1
    rw [Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp hp
  let g : G := ⟨GI.relabelPerm e p, giant hq⟩
  refine ⟨g, ?_⟩
  apply Equiv.ext
  intro v
  apply e.injective
  change e (g • v) = e (p v)
  rw [equivariant]
  change e (p (e.symm (e v))) = e (p v)
  rw [e.symm_apply_apply]

end GI.AlternatingActions

namespace GI.BudgetInduction

/-- The actual intransitive natural-stabilizer branch discharges the
Johnson alternative for every physical nongiant primitive action. -/
theorem primitive_alternative_of_intransitive_natural_stabilizer {m n : ℕ} {A₀ : ℝ}
    (G : Subgroup (Equiv.Perm (Fin m))) [MulAction G (Fin n)]
    [MulAction.IsPreprimitive G (Fin n)] [Nontrivial (Fin n)]
    (giant : alternatingGroup (Fin m) ≤ G) (hdegree : 3 ≤ m) (v : Fin n)
    (nongiant : ¬ alternatingGroup (Fin n) ≤ (MulAction.toPermHom G (Fin n)).range)
    (intransitive : ¬ MulAction.IsPretransitive
      ((MulAction.stabilizer G v).map G.subtype) (Fin m)) :
    PrimitiveReductionAlternative A₀ (MulAction.toPermHom G (Fin n)).range := by
  rcases AlternatingActions.natural_or_johnson_of_intransitive_stabilizer G giant
    (by simpa only [Fintype.card_fin] using hdegree) v intransitive with hnatural | hjohnson
  · obtain ⟨e, he⟩ := hnatural
    exact (nongiant (AlternatingActions.natural_coordinates_giant G giant e he)).elim
  · obtain ⟨t, ht, hhalf, e, _, himage⟩ := hjohnson
    exact Or.inr (Or.inr ⟨m, t, ht, by simpa only [Fintype.card_fin] using hhalf, e, himage⟩)

end GI.BudgetInduction
