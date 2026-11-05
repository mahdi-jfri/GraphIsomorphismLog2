module

public import Workspace.CoherentRectangleOutput

@[expose] public section

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

theorem colorClass_diagonal (c : Coloring n) (hc : Coherent c)
    (side : Bool) (x : Fin n) :
    colorClass c side x (c (side, x, x)) = {x} := by
  ext y
  rw [mem_colorClass, Finset.mem_singleton]
  constructor
  · intro h
    have hd := (hc (side, x, y) (side, x, x) h).1
    have hxy : x = y := by simpa [GI.PairRefinement.diagonal] using hd
    exact hxy.symm
  · intro h
    subst y
    rfl

theorem nontrivial_degree_ge_two (c : Coloring n) (side : Bool)
    (hn : NontrivialOffDiagonal c side) : 2 ≤ n := by
  obtain ⟨a, b, _, _, hab, _, _⟩ := hn
  by_contra h
  have ha := a.isLt
  have hb := b.isLt
  apply hab
  apply Fin.ext
  omega

/-- Dominance supplies its own non-diagonal fiber witness. No vertex in the
fiber needs to be assumed as an extra structural input. -/
theorem dominant_offDiagonal_witness (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hn : NontrivialOffDiagonal c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x) :
    ∃ a : ColorFiber c side x i, x ≠ a.val := by
  have hdegree := nontrivial_degree_ge_two c side hn
  have hdiag : i ≠ c (side, x, x) := by
    intro h
    subst i
    have hv : rowValency c side (c (side, x, x)) x = 1 := by
      rw [← colorClass_card, colorClass_diagonal c hc]
      simp
    omega
  have hpos : 0 < (colorClass c side x i).card := by
    rw [colorClass_card]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have he := (mem_colorClass c side x a i).mp ha
  refine ⟨⟨a, he⟩, ?_⟩
  intro h
  change x = a at h
  subst a
  exact hdiag he.symm

end GI.CoherentEntrance
