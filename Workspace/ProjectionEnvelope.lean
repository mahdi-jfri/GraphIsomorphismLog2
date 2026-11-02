import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Pi.Lemmas

namespace GI.PrimitiveCartesian

variable {I : Type*} {S : I → Type*} [∀ i, Group (S i)]

/-- The actual product of the coordinate images of a subgroup. -/
def projectionEnvelope (K : Subgroup (∀ i, S i)) : Subgroup (∀ i, S i) :=
  Subgroup.pi Set.univ (fun i => K.map (Pi.evalMonoidHom S i))

theorem le_projectionEnvelope (K : Subgroup (∀ i, S i)) : K ≤ projectionEnvelope K := by
  intro x hx i _
  exact ⟨x, hx, rfl⟩

theorem projectionEnvelope_ne_top (K : Subgroup (∀ i, S i)) (i : I)
    (proper : K.map (Pi.evalMonoidHom S i) ≠ ⊤) : projectionEnvelope K ≠ ⊤ := by
  classical
  intro ht
  apply proper
  apply top_le_iff.mp
  intro s _
  have hx : Pi.mulSingle i s ∈ projectionEnvelope K := by
    rw [ht]
    exact Subgroup.mem_top _
  simpa only [Pi.mulSingle_eq_same] using hx i (Set.mem_univ i)

/-- An actual automorphism that permutes coordinate fibers and preserves
the original subgroup also preserves the product of its coordinate images.
The finiteness assumption turns the proved inclusion into equality. -/
theorem projectionEnvelope_map_eq [Finite (∀ i, S i)]
    (K : Subgroup (∀ i, S i)) (e : MulAut (∀ i, S i)) (p : Equiv.Perm I)
    (fibers : ∀ i x y, x i = y i → e x (p i) = e y (p i))
    (preserves : K.map e.toMonoidHom = K) :
    (projectionEnvelope K).map e.toMonoidHom = projectionEnvelope K := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩ j _
    obtain ⟨i, rfl⟩ := p.surjective j
    obtain ⟨k, hk, hki⟩ := hx i (Set.mem_univ i)
    have hek : e k ∈ K := by
      rw [← preserves]
      exact ⟨k, hk, rfl⟩
    exact ⟨e k, hek, fibers i k x hki⟩
  · exact le_of_eq (Nat.card_congr (e.subgroupMap (projectionEnvelope K)).toEquiv)

end GI.PrimitiveCartesian

#print axioms GI.PrimitiveCartesian.projectionEnvelope
#print axioms GI.PrimitiveCartesian.le_projectionEnvelope
#print axioms GI.PrimitiveCartesian.projectionEnvelope_ne_top
#print axioms GI.PrimitiveCartesian.projectionEnvelope_map_eq
