import Workspace.CoherentFiberMatrix

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

def colorClass (c : Coloring n) (side : Bool) (x : Fin n) (i : Color n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => c (side, x, y) = i)

theorem mem_colorClass (c : Coloring n) (side : Bool) (x y : Fin n) (i : Color n) :
    y ∈ colorClass c side x i ↔ c (side, x, y) = i := by
  simp [colorClass]

theorem colorClass_card (c : Coloring n) (side : Bool) (x : Fin n) (i : Color n) :
    (colorClass c side x i).card = rowValency c side i x := rfl

theorem different_color_valencies_le (c : Coloring n) (side : Bool) (x : Fin n)
    (i j : Color n) (hij : i ≠ j) :
    rowValency c side i x + rowValency c side j x ≤ n := by
  have hd : Disjoint (colorClass c side x i) (colorClass c side x j) := by
    apply Finset.disjoint_left.mpr
    intro y hi hj
    exact hij (((mem_colorClass c side x y i).mp hi).symm.trans
      ((mem_colorClass c side x y j).mp hj))
  calc
    _ = (colorClass c side x i ∪ colorClass c side x j).card :=
      (Finset.card_union_of_disjoint hd).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

theorem dominant_color_unique (c : Coloring n) (side : Bool) (x : Fin n)
    (i j : Color n) (hi : n < 2 * rowValency c side i x)
    (hj : rowValency c side i x ≤ rowValency c side j x) : j = i := by
  by_contra hne
  have hsum := different_color_valencies_le c side x i j (Ne.symm hne)
  omega

/-- A vertex sees a dominant fiber in only one color only when that color
is itself the dominant color. Both valencies are actual relation counts. -/
theorem dominant_constant_column (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x)
    (a : ColorFiber c side x i) (r : Fin n)
    (constant : ∀ w : ColorFiber c side x i, c (side, w.val, r) = c (side, a.val, r)) :
    c (side, a.val, r) = i := by
  apply dominant_color_unique c side x i _ hi
  have hcols : rowValency c side i x ≤ columnValency c side (c (side, a.val, r)) r := by
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, constant ⟨w, (Finset.mem_filter.mp hw).2⟩⟩
  have hval : rowValency c side (c (side, a.val, r)) x =
      columnValency c side (c (side, a.val, r)) r := by
    rw [rowValency_constant c hc side hh a.val r x r]
    exact rowValency_eq_columnValency c hc side hh a.val r r
  rw [hval]
  exact hcols

theorem dominant_reverse (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x) (a : ColorFiber c side x i) :
    c (side, a.val, x) = i := by
  apply dominant_constant_column c hc side hh x i hi a x
  intro w
  exact (hc (side, x, w.val) (side, x, a.val) (w.property.trans a.property.symm)).2.1

theorem dominant_color_symmetric (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x) (a : ColorFiber c side x i)
    (u v : Fin n) (huv : c (side, u, v) = i) : c (side, v, u) = i := by
  have hrev := (hc (side, u, v) (side, x, a.val) (huv.trans a.property.symm)).2.1
  exact hrev.trans (dominant_reverse c hc side hh x i hi a)

end GI.CoherentEntrance

#print axioms GI.CoherentEntrance.different_color_valencies_le
#print axioms GI.CoherentEntrance.dominant_constant_column
#print axioms GI.CoherentEntrance.dominant_reverse
#print axioms GI.CoherentEntrance.dominant_color_symmetric
