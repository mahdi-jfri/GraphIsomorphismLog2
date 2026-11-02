import Workspace.CoherentMixedRectangle

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

theorem colorFiber_card (c : Coloring n) (side : Bool) (x : Fin n) (i : Color n) :
    Fintype.card (ColorFiber c side x i) = rowValency c side i x :=
  Fintype.card_subtype _

theorem colorClasses_disjoint (c : Coloring n) (side : Bool) (x : Fin n)
    (i j : Color n) (hij : i ≠ j) :
    Disjoint (colorClass c side x i) (colorClass c side x j) := by
  apply Finset.disjoint_left.mpr
  intro y hi hj
  exact hij (((mem_colorClass c side x y i).mp hi).symm.trans
    ((mem_colorClass c side x y j).mp hj))

/-- Exact physical rectangle output in the dominant primitive-color branch.
The sides are genuine color fibers; nontriviality and the twin bound are derived. -/
theorem dominant_rectangle_output (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    (hp : PrimitiveColorCuts c side) (x : Fin n) (i : Color n)
    (hi : n < 2 * rowValency c side i x)
    (a : ColorFiber c side x i) (hxa : x ≠ a.val) :
    ∃ j : Color n, j ≠ i ∧ j ≠ c (side, x, x) ∧
      ∃ b : ColorFiber c side x j, ∃ k : Color n,
      (∀ u : ColorFiber c side x i,
        Semiregular.rowDegree (fiberMatrix c side x i j k) u =
          Semiregular.rowDegree (fiberMatrix c side x i j k) a) ∧
      (∀ r : ColorFiber c side x j,
        Semiregular.columnDegree (fiberMatrix c side x i j k) r =
          Semiregular.columnDegree (fiberMatrix c side x i j k) b) ∧
      (∃ u w : ColorFiber c side x i,
        fiberMatrix c side x i j k u b = true ∧ fiberMatrix c side x i j k w b = false) ∧
      (∀ u : ColorFiber c side x i,
        2 * (Semiregular.twins (fiberMatrix c side x i j k) u).card ≤ rowValency c side i x) ∧
      rowValency c side i x + rowValency c side j x ≤ n ∧
      Disjoint (colorClass c side x i) (colorClass c side x j) := by
  obtain ⟨j, hji, hjdiag, b, k, u, w, he, hne⟩ :=
    dominant_mixed_rectangle c hc side hh hn hp x i hi a hxa
  obtain ⟨rows, columns⟩ := fiberMatrix_semiregular c hc side x i j k a b
  refine ⟨j, hji, hjdiag, b, k, rows, columns, ⟨u, w, he, hne⟩, ?_,
    different_color_valencies_le c side x i j (Ne.symm hji),
    colorClasses_disjoint c side x i j (Ne.symm hji)⟩
  intro z
  have ht := Semiregular.nontrivial_twins_half (fiberMatrix c side x i j k)
    _ _ rows columns ⟨u, b, he⟩ ⟨w, b, hne⟩ z
  simpa only [colorFiber_card] using ht

/-- Every actual parent color transporter restricts to bijections of the
actual color fibers at its source vertex and target image. -/
def fiberTransport (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) (h : GI.PairRefinement.Transports c source target p)
    (x : Fin n) (i : Color n) :
    ColorFiber c source x i ≃ ColorFiber c target (p x) i where
  toFun y := ⟨p y.val, (h x y.val).trans y.property⟩
  invFun z := ⟨p.symm z.val, by
    have he : c (target, p x, z.val) = c (source, x, p.symm z.val) := by
      simpa only [Equiv.apply_symm_apply] using h x (p.symm z.val)
    exact he.symm.trans z.property⟩
  left_inv y := Subtype.ext (p.symm_apply_apply y.val)
  right_inv z := Subtype.ext (p.apply_symm_apply z.val)

theorem fiberMatrix_transport (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) (h : GI.PairRefinement.Transports c source target p)
    (x : Fin n) (i j k : Color n)
    (w : ColorFiber c source x i) (r : ColorFiber c source x j) :
    fiberMatrix c target (p x) i j k (fiberTransport c source target p h x i w)
      (fiberTransport c source target p h x j r) = fiberMatrix c source x i j k w r := by
  change decide (c (target, p w.val, p r.val) = k) = decide (c (source, w.val, r.val) = k)
  rw [h w.val r.val]

end GI.CoherentEntrance

#print axioms GI.CoherentEntrance.dominant_rectangle_output
#print axioms GI.CoherentEntrance.fiberTransport
#print axioms GI.CoherentEntrance.fiberMatrix_transport
