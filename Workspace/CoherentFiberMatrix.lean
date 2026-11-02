import Workspace.CoherentValencies

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

abbrev ColorFiber (c : Coloring n) (side : Bool) (x : Fin n) (i : Color n) :=
  { y : Fin n // c (side, x, y) = i }

def fiberMatrix (c : Coloring n) (side : Bool) (x : Fin n)
    (i j k : Color n) (w : ColorFiber c side x i) (r : ColorFiber c side x j) : Bool :=
  decide (c (side, w.val, r.val) = k)

theorem fiber_row_intersection (c : Coloring n) (hc : Coherent c)
    (side : Bool) (x : Fin n) (i j k : Color n)
    (b : ColorFiber c side x j) (w : ColorFiber c side x i) :
    Semiregular.rowDegree (fiberMatrix c side x i j k) w =
      intersection c (side, w.val, x) k (c (side, b.val, x)) := by
  unfold Semiregular.rowDegree intersection
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    have hcr : c (side, w.val, r.val) = k := by
      simpa [fiberMatrix] using hr
    have hrev : c (side, r.val, x) = c (side, b.val, x) := by
      simpa only [transpose] using
        (hc (side, x, r.val) (side, x, b.val) (r.property.trans b.property.symm)).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcr, hrev⟩
  · intro r _ s _ h
    exact Subtype.ext h
  · intro r hr
    have h := (Finset.mem_filter.mp hr).2
    have hxr : c (side, x, r) = j := by
      have hrev := (hc (side, r, x) (side, b.val, x) h.2).2.1
      exact hrev.trans b.property
    refine ⟨⟨r, hxr⟩, ?_, rfl⟩
    simpa [fiberMatrix] using h.1

theorem fiber_column_intersection (c : Coloring n)
    (side : Bool) (x : Fin n) (i j k : Color n)
    (r : ColorFiber c side x j) :
    Semiregular.columnDegree (fiberMatrix c side x i j k) r =
      intersection c (side, x, r.val) i k := by
  unfold Semiregular.columnDegree intersection
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    have hcw : c (side, w.val, r.val) = k := by
      simpa [fiberMatrix] using hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property, hcw⟩
  · intro w _ v _ h
    exact Subtype.ext h
  · intro w hw
    have h := (Finset.mem_filter.mp hw).2
    refine ⟨⟨w, h.1⟩, ?_, rfl⟩
    simpa [fiberMatrix] using h.2

/-- Between two actual color fibers of one source vertex, every color
relation is semiregular. The row and column regularity follow from coherence. -/
theorem fiberMatrix_semiregular (c : Coloring n) (hc : Coherent c)
    (side : Bool) (x : Fin n) (i j k : Color n)
    (a : ColorFiber c side x i) (b : ColorFiber c side x j) :
    (∀ w : ColorFiber c side x i,
      Semiregular.rowDegree (fiberMatrix c side x i j k) w =
        Semiregular.rowDegree (fiberMatrix c side x i j k) a) ∧
    (∀ r : ColorFiber c side x j,
      Semiregular.columnDegree (fiberMatrix c side x i j k) r =
        Semiregular.columnDegree (fiberMatrix c side x i j k) b) := by
  constructor
  · intro w
    rw [fiber_row_intersection c hc side x i j k b w,
      fiber_row_intersection c hc side x i j k b a]
    have hrev : c (side, w.val, x) = c (side, a.val, x) := by
      simpa only [transpose] using
        (hc (side, x, w.val) (side, x, a.val) (w.property.trans a.property.symm)).2.1
    exact (hc (side, w.val, x) (side, a.val, x) hrev).2.2 _ _
  · intro r
    rw [fiber_column_intersection, fiber_column_intersection]
    exact (hc (side, x, r.val) (side, x, b.val)
      (r.property.trans b.property.symm)).2.2 _ _

end GI.CoherentEntrance

#print axioms GI.CoherentEntrance.fiber_row_intersection
#print axioms GI.CoherentEntrance.fiber_column_intersection
#print axioms GI.CoherentEntrance.fiberMatrix_semiregular
