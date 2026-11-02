import Workspace.Impl.GenNormInc
import Workspace.Impl.Weights

/-!
# The exact label value of a normalization child

The Cameron table gives the Johnson block at each domain point. We complement each block
when `2k > m`, and use the size of the fiber over block zero. The resulting value carries
exactly `N.childLabels j` for every coset, including the selected interval and the point
homomorphism. It is independent of the target coloring of the child.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {Ω C : Type} {S : State Ω C} {n : ℕ}

/-- The indicators of the Cameron blocks, complemented when needed and empty off the domain. -/
noncomputable def normBlockMapVal (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (c : Q.NormChoice) : Val := by
  classical
  exact .list ((List.finRange n).map fun i =>
    if en.symm i ∈ S.dom then encFun (fun j : Fin c.m =>
      if j ∈ (if 2 * c.k ≤ c.m then Q.kset c.e (en.symm i) else
        (Q.kset c.e (en.symm i))ᶜ) then 1 else 0)
    else .list [])

/-- The target label value, from the chosen Cameron factor and graph generators. -/
noncomputable def normLabelVal (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (c : Q.NormChoice) (ps : List (Perm (Fin n) × Perm (Fin c.m))) : Val :=
  .list [.nat c.m, .list (ps.map fun p => .list [encPerm p.1, encPerm p.2]),
    .nat Q.pre.length, .nat (if 2 * c.k ≤ c.m then c.k else c.m - c.k),
    .nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}),
    normBlockMapVal en Q c]

private theorem normComplIndicator {m : ℕ} (A : Finset (Fin m)) (t : Fin m) :
    (if t ∈ Aᶜ then (1 : ℕ) else 0) = if t ∈ A then 0 else 1 := by
  classical
  simp only [Finset.mem_compl, ite_not]

/-- The block table is the one stored by the model's supplied labels. -/
theorem normBlockMapVal_eq [Finite Ω] {P : Params} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (c : Q.NormChoice) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) :
    blkMapVal en ((Q.normAboveOf c htr hq hkc hkl).childLabels j).con.blocks =
      normBlockMapVal en Q c := by
  classical
  by_cases hk : 2 * c.k ≤ c.m
  · simp [NormAbove.childLabels, NormAbove.labels, PrimitiveQuotient.normAboveOf,
      PrimitiveQuotient.constituent, hk, PrimitiveQuotient.johnsonBlocks,
      PrimitiveQuotient.Flip.id, blkMapVal, normBlockMapVal, NormAbove.child,
      PrimitiveQuotient.normalizationOf, State.restrict]
    intro a
    rfl
  · simp [NormAbove.childLabels, NormAbove.labels, PrimitiveQuotient.normAboveOf,
      PrimitiveQuotient.constituent, hk, PrimitiveQuotient.johnsonBlocks,
      PrimitiveQuotient.Flip.compl, blkMapVal, normBlockMapVal, NormAbove.child,
      PrimitiveQuotient.normalizationOf, State.restrict]
    intro a
    by_cases ha : en.symm a ∈ S.dom
    · simp only [ha, if_true]
      congr 1
      funext t
      change Fin c.m at t
      exact normComplIndicator (Q.kset c.e (en.symm a)) t
    · simp only [ha, if_false]

/-- Any bounded generating list with the recovered point images gives `LabValStd` of exactly
the child's supplied labels. -/
theorem normLabelVal_spec [Finite Ω] {P : Params} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (c : Q.NormChoice) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (ps : List (Perm (Fin n) × Perm (Fin c.m)))
    (hlen : ps.length ≤ n ^ 2)
    (hgen : gens (ps.map Prod.fst) = groupFin en (Q.normGroup c.e c.hS))
    (hps : ∀ p ∈ ps, ∀ hg : (toFin en).symm p.1 ∈ Q.normGroup c.e c.hS,
      ((Q.normPi c.e c.hS ⟨(toFin en).symm p.1, hg⟩ : alternatingGroup (Fin c.m)) :
        Perm (Fin c.m)) = p.2)
    (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) :
    LabValStd en ((Q.normAboveOf c htr hq hkc hkl).child j) (normLabelVal en Q c ps)
      ((Q.normAboveOf c htr hq hkc hkl).childLabels j) := by
  classical
  refine ⟨ps, ?_, hlen, hgen, hps⟩
  have hb := normBlockMapVal_eq en Q c htr hq hkc hkl j
  rw [hb]
  by_cases hk : 2 * c.k ≤ c.m
  · simp [normLabelVal, NormAbove.childLabels, NormAbove.labels,
      PrimitiveQuotient.normAboveOf, PrimitiveQuotient.normalizationOf,
      PrimitiveQuotient.constituent, hk, PrimitiveQuotient.johnsonBlocks,
      PrimitiveQuotient.Flip.id, Normalization.labels]
  · simp [normLabelVal, NormAbove.childLabels, NormAbove.labels,
      PrimitiveQuotient.normAboveOf, PrimitiveQuotient.normalizationOf,
      PrimitiveQuotient.constituent, hk, PrimitiveQuotient.johnsonBlocks,
      PrimitiveQuotient.Flip.compl, Normalization.labels]

/-- The exact label value has the standard polynomial weight bound. -/
theorem normLabelVal_wt_le [Finite Ω] {P : Params} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (c : Q.NormChoice) (htr : S.Transitive)
    (hq : P.q₀ < (Q.normalizationOf c).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (ps : List (Perm (Fin n) × Perm (Fin c.m)))
    (hlen : ps.length ≤ n ^ 2)
    (hgen : gens (ps.map Prod.fst) = groupFin en (Q.normGroup c.e c.hS))
    (hps : ∀ p ∈ ps, ∀ hg : (toFin en).symm p.1 ∈ Q.normGroup c.e c.hS,
      ((Q.normPi c.e c.hS ⟨(toFin en).symm p.1, hg⟩ : alternatingGroup (Fin c.m)) :
        Perm (Fin c.m)) = p.2)
    (hs : SmallInv S) (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) :
    (normLabelVal en Q c ps).wt ≤ labWStd n S.N := by
  have h := normLabelVal_spec en Q c htr hq hkc hkl ps hlen hgen hps j
  exact h.wt_le (normChild_smallInv Q c htr hq hkc hkl hs j).small.1

end GI.Impl
