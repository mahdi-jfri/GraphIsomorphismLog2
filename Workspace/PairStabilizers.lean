import Workspace.PairActions

namespace GI.Pairs

open Equiv Equiv.Perm
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

def pointwise (a b : α) (hab : a ≠ b) : Subgroup (alternatingGroup α) :=
  MulAction.stabilizer (alternatingGroup α) (⟨(a, b), hab⟩ : OrderedPair α)

def setwise (a b : α) (hab : a ≠ b) : Subgroup (alternatingGroup α) :=
  MulAction.stabilizer (alternatingGroup α) (unorderedOfOrdered ⟨(a, b), hab⟩)

theorem mem_pointwise (a b : α) (hab : a ≠ b) (g : alternatingGroup α) :
    g ∈ pointwise a b hab ↔ (g : Perm α) a = a ∧ (g : Perm α) b = b := by
  change g • (⟨(a, b), hab⟩ : OrderedPair α) = ⟨(a, b), hab⟩ ↔ _
  rw [Subtype.ext_iff]
  change (g.val a, g.val b) = (a, b) ↔ _
  simp only [Prod.mk.injEq]

theorem mem_setwise (a b : α) (hab : a ≠ b) (g : alternatingGroup α) :
    g ∈ setwise a b hab ↔
      ((g : Perm α) a = a ∧ (g : Perm α) b = b) ∨
      ((g : Perm α) a = b ∧ (g : Perm α) b = a) := by
  change g • unorderedOfOrdered (⟨(a, b), hab⟩ : OrderedPair α) =
    unorderedOfOrdered ⟨(a, b), hab⟩ ↔ _
  rw [Subtype.ext_iff]
  change (g : Perm α) • ({a, b} : Finset α) = {a, b} ↔ _
  have hpair : (g : Perm α) • ({a, b} : Finset α) = {g.val a, g.val b} := by
    simp [Finset.smul_finset_def]
  rw [hpair, ← Finset.coe_inj]
  simp only [Finset.coe_pair, Set.pair_eq_pair_iff]

theorem pointwise_le_setwise (a b : α) (hab : a ≠ b) :
    pointwise a b hab ≤ setwise a b hab := by
  intro g hg
  exact (mem_setwise a b hab g).mpr (Or.inl ((mem_pointwise a b hab g).mp hg))

/-- There is no intermediate subgroup between the pointwise and setwise
stabilizers of a pair. This proves the dichotomy directly, without an index
classification theorem or an assumption about quotient order. -/
theorem stabilizer_dichotomy (a b : α) (hab : a ≠ b)
    (P : Subgroup (alternatingGroup α))
    (lower : pointwise a b hab ≤ P) (upper : P ≤ setwise a b hab) :
    P = pointwise a b hab ∨ P = setwise a b hab := by
  by_cases hsmall : P ≤ pointwise a b hab
  · exact Or.inl (hsmall.antisymm lower)
  · have hex : ∃ u : alternatingGroup α, u ∈ P ∧ u ∉ pointwise a b hab := by
      by_contra hn
      push Not at hn
      exact hsmall (fun u hu => hn u hu)
    obtain ⟨u, hu, hnot⟩ := hex
    have huswap : (u : Perm α) a = b ∧ (u : Perm α) b = a := by
      rcases (mem_setwise a b hab u).mp (upper hu) with hfix | hswap
      · exact (hnot ((mem_pointwise a b hab u).mpr hfix)).elim
      · exact hswap
    refine Or.inr (upper.antisymm ?_)
    intro v hv
    rcases (mem_setwise a b hab v).mp hv with hfix | hswap
    · exact lower ((mem_pointwise a b hab v).mpr hfix)
    · have hdiff : u⁻¹ * v ∈ pointwise a b hab := by
        apply (mem_pointwise a b hab _).mpr
        constructor
        · change (u : Perm α)⁻¹ ((v : Perm α) a) = a
          rw [hswap.1, ← huswap.1]
          exact (u : Perm α).symm_apply_apply a
        · change (u : Perm α)⁻¹ ((v : Perm α) b) = b
          rw [hswap.2, ← huswap.2]
          exact (u : Perm α).symm_apply_apply b
      have h := P.mul_mem hu (lower hdiff)
      simpa only [mul_inv_cancel_left] using h

end GI.Pairs
