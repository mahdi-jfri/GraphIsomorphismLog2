module

public import Workspace.AlternatingSubsetTransitive
public import Workspace.PrimitiveActionCoordinates
public import Workspace.IntransitiveInvariantSubset

@[expose] public section

namespace GI.AlternatingActions

open scoped Pointwise

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every nonempty proper fixed-size subset space has at least two
vertices, witnessed by moving an element outside the chosen subset. -/
theorem subsetVertex_nontrivial (s : Finset A) (hpos : 1 ≤ s.card)
    (hproper : s.card < Fintype.card A) : Nontrivial (Johnson.SubsetVertex A s.card) := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hcomp : 0 < sᶜ.card := by rw [Finset.card_compl]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcomp
  have hy' : y ∉ s := Finset.mem_compl.mp hy
  let u : Johnson.SubsetVertex A s.card := ⟨s, rfl⟩
  let v := Johnson.subsetAction s.card (Equiv.swap x y) u
  refine ⟨⟨u, v, ?_⟩⟩
  intro he
  have hm : y ∈ (Equiv.swap x y) • s := by
    simpa using (Finset.smul_mem_smul_finset_iff (Equiv.swap x y)).mpr hx
  have hs := congrArg Subtype.val he
  change s = (Equiv.swap x y) • s at hs
  exact hy' (hs ▸ hm)

variable {V : Type*} (G : Subgroup (Equiv.Perm A)) [MulAction G V]
  [Nontrivial V] [MulAction.IsPreprimitive G V]

/-- An actual nontrivial subset invariant under a physical point
stabilizer yields equivariant coordinates on the whole physical action.
Maximality derives stabilizer equality; subset transitivity is proved
from the actual alternating subgroup inclusion. -/
theorem coordinates_of_invariant_finset
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Fintype.card A)
    (a : V) (s : Finset A) (hpos : 1 ≤ s.card) (hproper : s.card < Fintype.card A)
    (hinvariant : ∀ g ∈ MulAction.stabilizer G a, (g : Equiv.Perm A) • s = s) :
    ∃ e : V ≃ Johnson.SubsetVertex A s.card, ∀ (g : G) (v : V),
      e (g • v) = Johnson.subsetAction s.card (g : Equiv.Perm A) (e v) := by
  letI := subset_pretransitive G giant hdegree s.card
  letI := subsetVertex_nontrivial s hpos hproper
  let b : Johnson.SubsetVertex A s.card := ⟨s, rfl⟩
  have hle : MulAction.stabilizer G a ≤ MulAction.stabilizer G b := by
    intro g hg
    exact Subtype.ext (hinvariant g hg)
  have heq := GI.PrimitiveCoordinates.primitive_stabilizer_eq a b hle
  refine ⟨GI.PrimitiveCoordinates.sameStabilizerCoordinates a b heq, ?_⟩
  exact GI.PrimitiveCoordinates.sameStabilizerCoordinates_equivariant a b heq

/-- An intransitive physical point stabilizer in the explicit natural
alternating/symmetric realization forces a natural or Johnson subset
action on the physical domain, with subset size at most half the degree. -/
theorem coordinates_of_intransitive_stabilizer
    (giant : alternatingGroup A ≤ G) (hdegree : 3 ≤ Fintype.card A) (a : V)
    (intransitive : ¬ MulAction.IsPretransitive
      ((MulAction.stabilizer G a).map G.subtype) A) :
    ∃ t : ℕ, 1 ≤ t ∧ 2 * t ≤ Fintype.card A ∧
      ∃ e : V ≃ Johnson.SubsetVertex A t, ∀ (g : G) (v : V),
        e (g • v) = Johnson.subsetAction t (g : Equiv.Perm A) (e v) := by
  obtain ⟨s, hpos, hhalf, hinv⟩ := exists_small_invariant_finset
    ((MulAction.stabilizer G a).map G.subtype) intransitive
  have hproper : s.card < Fintype.card A := by omega
  refine ⟨s.card, hpos, hhalf, ?_⟩
  apply coordinates_of_invariant_finset G giant hdegree a s hpos hproper
  intro g hg
  exact hinv ⟨g.val, ⟨g, hg, rfl⟩⟩

end GI.AlternatingActions
