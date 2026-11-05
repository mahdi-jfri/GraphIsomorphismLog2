module

public import Workspace.CoherentUniformComponents
public import Workspace.BlockPartition

@[expose] public section

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

theorem colorReach_transport (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) (h : GI.PairRefinement.Transports c source target p)
    (k : Color n) {x y : Fin n} (hxy : colorReach c source k x y) :
    colorReach c target k (p x) (p y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d _ hbd ih =>
    apply ih.tail
    rcases hbd with he | he
    · exact Or.inl ((h b d).trans he)
    · exact Or.inr ((h d b).trans he)

def colorPartition (c : Coloring n) (side : Bool) (k : Color n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ h : H, GI.PairRefinement.Transports c side side h.val) :
    GI.InvariantPartition H where
  setoid := ⟨colorReach c side k, colorReach_equivalence c side k⟩
  preserved h _ _ hxy := colorReach_transport c side side h.val (hH h) k hxy

theorem colorPartition_same_block (c : Coloring n) (side : Bool) (k : Color n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ h : H, GI.PairRefinement.Transports c side side h.val) (x y : Fin n) :
    (colorPartition c side k H hH).blockCover.label x =
      (colorPartition c side k H hH).blockCover.label y ↔
        y ∈ colorComponent c side k x := by
  rw [GI.InvariantPartition.same_block_iff, mem_colorComponent]
  rfl

/-- Failure of color-cut connectedness yields actual equal-sized, nontrivial,
balanced component blocks. The partition is defined by the input colors. -/
theorem nonprimitive_balanced_components (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (hp : ¬ PrimitiveColorCuts c side) :
    ∃ a b : Fin n, a ≠ b ∧
      (∀ x y, (colorComponent c side (c (side, a, b)) x).card =
        (colorComponent c side (c (side, a, b)) y).card) ∧
      (∀ x, 2 ≤ (colorComponent c side (c (side, a, b)) x).card ∧
        2 * (colorComponent c side (c (side, a, b)) x).card ≤ n) := by
  classical
  simp only [PrimitiveColorCuts, not_forall, Classical.not_imp] at hp
  obtain ⟨a, b, hab, S, hne, hproper, hcut⟩ := hp
  obtain ⟨u, hu⟩ := hne
  have hout : ∃ v, v ∉ S := by
    by_contra hv
    apply hproper
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hvmem
    exact hv ⟨v, hvmem⟩
  obtain ⟨v, hv⟩ := hout
  have hclosed : ∀ x ∈ S, ∀ y ∉ S, ¬ colorEdge c side (c (side, a, b)) x y := by
    intro x hx y hy he
    exact hcut ⟨x, hx, y, hy, he⟩
  have huv : ¬ colorReach c side (c (side, a, b)) u v := by
    intro he
    exact hv (colorReach_stays_in_cut c side _ S hclosed hu he)
  refine ⟨a, b, hab, colorComponent_card_eq c hc side hh _, ?_⟩
  intro x
  exact ⟨colorComponent_nontrivial c hc side hh a b hab x,
    colorComponent_half c hc side hh _ u v huv x⟩

end GI.CoherentEntrance
