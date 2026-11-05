module

public import Workspace.DominantColor
public import Workspace.CoherentCliqueBound

@[expose] public section

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

theorem mixed_column_of_crossing (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x)
    (a : ColorFiber c side x i) (r : Fin n)
    (hr : r ∉ colorClass c side x i) (har : c (side, a.val, r) ≠ i) :
    ∃ j : Color n, j ≠ i ∧ j ≠ c (side, x, x) ∧
      ∃ b : ColorFiber c side x j, ∃ k : Color n, ∃ w : ColorFiber c side x i,
        fiberMatrix c side x i j k a b = true ∧
        fiberMatrix c side x i j k w b = false := by
  have hrx : r ≠ x := by
    intro h
    subst r
    exact har (dominant_reverse c hc side hh x i hi a)
  have hji : c (side, x, r) ≠ i := by
    intro h
    exact hr ((mem_colorClass c side x r i).mpr h)
  have hjdiag : c (side, x, r) ≠ c (side, x, x) :=
    Ne.symm (offDiagonal_loop_ne c hc side x r x (Ne.symm hrx))
  have hvar : ∃ w : ColorFiber c side x i,
      c (side, w.val, r) ≠ c (side, a.val, r) := by
    by_contra h
    apply har
    apply dominant_constant_column c hc side hh x i hi a r
    intro w
    by_contra hw
    exact h ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hvar
  refine ⟨c (side, x, r), hji, hjdiag, ⟨r, rfl⟩, c (side, a.val, r), w, ?_, ?_⟩
  · simp [fiberMatrix]
  · simpa [fiberMatrix] using hw

/-- The cut formulation of connectedness for every occurring off-diagonal
color relation (with its reverse). This is a property of the configuration,
not an assumption about the size of its automorphism group. -/
def PrimitiveColorCuts (c : Coloring n) (side : Bool) : Prop :=
  ∀ a b : Fin n, a ≠ b → ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ u ∈ S, ∃ v ∉ S,
      c (side, u, v) = c (side, a, b) ∨ c (side, v, u) = c (side, a, b)

/-- A connected nontrivial homogeneous coherent configuration supplies an
actual second color fiber and an actual mixed binary matrix at its dominant
fiber. It does not require a matrix or its nontriviality as an input. -/
theorem dominant_mixed_rectangle (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    (hp : PrimitiveColorCuts c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x)
    (a : ColorFiber c side x i) (hxa : x ≠ a.val) :
    ∃ j : Color n, j ≠ i ∧ j ≠ c (side, x, x) ∧
      ∃ b : ColorFiber c side x j, ∃ k : Color n,
      ∃ u w : ColorFiber c side x i,
        fiberMatrix c side x i j k u b = true ∧
        fiberMatrix c side x i j k w b = false := by
  obtain ⟨z, t, hzt, hother⟩ := exists_other_offDiagonal_color c side hn i
  have hne : (colorClass c side x i).Nonempty :=
    ⟨a.val, (mem_colorClass c side x a.val i).mpr a.property⟩
  have hx : x ∉ colorClass c side x i := by
    intro h
    exact offDiagonal_loop_ne c hc side x a.val x hxa
      (((mem_colorClass c side x x i).mp h).trans a.property.symm)
  have hproper : colorClass c side x i ≠ Finset.univ := by
    intro h
    apply hx
    rw [h]
    exact Finset.mem_univ _
  obtain ⟨u, hu, v, hv, hedge⟩ := hp z t hzt _ hne hproper
  let u' : ColorFiber c side x i := ⟨u, (mem_colorClass c side x u i).mp hu⟩
  have hrare : c (side, u, v) ≠ i := by
    intro he
    rcases hedge with he' | he'
    · exact hother (he'.symm.trans he)
    · exact hother (he'.symm.trans (dominant_color_symmetric c hc side hh x i hi a u v he))
  obtain ⟨j, hji, hjdiag, b, k, w, htrue, hfalse⟩ :=
    mixed_column_of_crossing c hc side hh x i hi u' v hv hrare
  exact ⟨j, hji, hjdiag, b, k, u', w, htrue, hfalse⟩

end GI.CoherentEntrance
