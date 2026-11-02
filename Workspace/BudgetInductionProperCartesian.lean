import Workspace.PrimitiveUniformCoordinates
import Workspace.FiniteCartesianWitness
import Workspace.BudgetInductionAlternatives

namespace GI.BudgetInduction

open GI.RadicalSocle GI.PrimitiveCartesian

variable {n : ℕ} {A₀ : ℝ} (H : Subgroup (Equiv.Perm (Fin n)))
  [Nontrivial (Fin n)] [MulAction.IsPreprimitive H (Fin n)]

/-- The proper-projection branch of an actual nonsimple minimal normal
subgroup yields the existing Cartesian alternative. Every conjugacy,
coordinate equivalence, position action and component action is derived. -/
theorem cartesian_alternative_of_minimalNormal_proper_projection
    (radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup H) [N.Normal] (hN : MinimalNormal N) (a : Fin n)
    (factorCount : 2 ≤ Nat.card (MinimalNormals N)) (i : MinimalNormals N)
    (proper : ((MulAction.stabilizer H a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤) :
    PrimitiveReductionAlternative A₀ H := by
  let K := (MulAction.stabilizer H a).comap (minimalCoordinateEmbedding radicalFree N hN)
  let Q := K.map (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i)
  let D := i.val ⧸ Q
  letI := Fintype.ofFinite (MinimalNormals N)
  letI := Fintype.ofFinite D
  have hd : 2 ≤ Fintype.card D := by
    have h : 2 ≤ Q.index := Nat.succ_le_iff.mpr (Q.one_lt_index_of_ne_top proper)
    change 2 ≤ Nat.card D at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hi : 2 ≤ Fintype.card (MinimalNormals N) := by
    simpa only [Nat.card_eq_fintype_card] using factorCount
  exact Or.inr (Or.inl (CartesianCoordinates.finite_cartesian_witness H
    (primitiveUniformCoordinates radicalFree N hN a i proper) (normalFactorPositions N)
    (primitiveUniformCoordinates_fibers radicalFree N hN a i proper) hd hi))

/-- Consequently every remaining unsupported nonsimple-minimal branch
has an actual subdirect socle point stabilizer. -/
theorem unsupported_minimalNormal_projections_surjective
    (radicalFree : ∀ K : Subgroup H, K.Normal → IsSolvable K → K = ⊥)
    (N : Subgroup H) [N.Normal] (hN : MinimalNormal N) (a : Fin n)
    (factorCount : 2 ≤ Nat.card (MinimalNormals N))
    (unsupported : ¬ PrimitiveReductionAlternative A₀ H) :
    ∀ i : MinimalNormals N, ((MulAction.stabilizer H a).comap
      (minimalCoordinateEmbedding radicalFree N hN)).map
        (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) = ⊤ := by
  intro i
  by_contra hproper
  exact unsupported (cartesian_alternative_of_minimalNormal_proper_projection H
    radicalFree N hN a factorCount i hproper)

end GI.BudgetInduction

#print axioms GI.BudgetInduction.cartesian_alternative_of_minimalNormal_proper_projection
#print axioms GI.BudgetInduction.unsupported_minimalNormal_projections_surjective
