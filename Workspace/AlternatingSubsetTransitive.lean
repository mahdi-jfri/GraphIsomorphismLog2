module

public import Workspace.JohnsonAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

namespace GI.AlternatingActions

open scoped Pointwise
open Equiv Equiv.Perm

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Equal-cardinality finite subsets are carried to one another by an
actual permutation extending an equivalence of their elements. -/
theorem exists_perm_finset_eq (s t : Finset A) (hcard : s.card = t.card) :
    ∃ p : Perm A, p • s = t := by
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using hcard)
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hy
    exact e.extendSubtype_mem x hx
  · rw [Finset.card_smul_finset, hcard]

/-- In degree at least three every subset is fixed by an odd permutation:
a transposition inside it or inside its complement. -/
theorem exists_odd_finset_stabilizer (hdegree : 3 ≤ Fintype.card A) (s : Finset A) :
    ∃ q : Perm A, q.sign = -1 ∧ q • s = s := by
  have build : ∀ a b : A, a ≠ b → (a ∈ s ↔ b ∈ s) →
      ∃ q : Perm A, q.sign = -1 ∧ q • s = s := by
    intro a b hab hmem
    refine ⟨swap a b, Perm.sign_swap hab, ?_⟩
    apply Finset.coe_injective
    rw [Finset.coe_smul_finset]
    exact Equiv.swap_mem_stabilizer.mpr hmem
  by_cases hs : 2 ≤ s.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
    exact build a b hab (iff_of_true ha hb)
  · have hc : 2 ≤ sᶜ.card := by rw [Finset.card_compl]; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    exact build a b hab (iff_of_false (Finset.mem_compl.mp ha) (Finset.mem_compl.mp hb))

/-- The alternating group is transitive on every fixed-cardinality
subset space in degree at least three, proved by correcting parity. -/
theorem exists_alternating_finset_eq (hdegree : 3 ≤ Fintype.card A)
    (s t : Finset A) (hcard : s.card = t.card) :
    ∃ p : alternatingGroup A, (p : Perm A) • s = t := by
  obtain ⟨p, hp⟩ := exists_perm_finset_eq s t hcard
  rcases Int.units_eq_one_or p.sign with hsign | hsign
  · exact ⟨⟨p, mem_alternatingGroup.mpr hsign⟩, hp⟩
  · obtain ⟨q, hqsign, hq⟩ := exists_odd_finset_stabilizer hdegree s
    refine ⟨⟨p * q, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, map_mul, hsign, hqsign, Int.units_mul_self]
    · change (p * q) • s = t
      rw [mul_smul, hq, hp]

/-- The physical fixed-cardinality subset action of an actual subgroup. -/
instance subsetMulAction (G : Subgroup (Perm A)) (t : ℕ) :
    MulAction G (Johnson.SubsetVertex A t) :=
  MulAction.compHom _ ((Johnson.subsetAction t).comp G.subtype)

omit [Fintype A] in
@[simp] theorem subset_smul_val (G : Subgroup (Perm A)) (t : ℕ)
    (g : G) (s : Johnson.SubsetVertex A t) :
    (g • s).val = (g : Perm A) • s.val := rfl

theorem subset_pretransitive (G : Subgroup (Perm A))
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Fintype.card A) (t : ℕ) :
    MulAction.IsPretransitive G (Johnson.SubsetVertex A t) := by
  constructor
  intro s u
  obtain ⟨p, hp⟩ := exists_alternating_finset_eq hdegree s.val u.val
    (s.property.trans u.property.symm)
  exact ⟨⟨p.val, giant p.property⟩, Subtype.ext hp⟩

end GI.AlternatingActions
