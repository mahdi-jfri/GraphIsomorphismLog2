import Workspace.CoherentDominantWitness
import Workspace.Parameters

namespace GI.CoherentEntrance

open GI.PairRefinement

variable {n : ℕ}

/-- The physical first-entrance rectangle, including its actual colors,
fiber vertices, semiregularity, twin bound and area bound. -/
structure RectangleCertificate (c : Coloring n) (side : Bool) (x : Fin n) (eta : ℝ) where
  leftColor : Color n
  rightColor : Color n
  edgeColor : Color n
  leftPoint : ColorFiber c side x leftColor
  rightPoint : ColorFiber c side x rightColor
  dominant : eta * n < (rowValency c side leftColor x : ℝ)
  different : rightColor ≠ leftColor
  leftOffDiagonal : leftColor ≠ c (side, x, x)
  rightOffDiagonal : rightColor ≠ c (side, x, x)
  rows : ∀ u, Semiregular.rowDegree (fiberMatrix c side x leftColor rightColor edgeColor) u =
    Semiregular.rowDegree (fiberMatrix c side x leftColor rightColor edgeColor) leftPoint
  columns : ∀ r, Semiregular.columnDegree (fiberMatrix c side x leftColor rightColor edgeColor) r =
    Semiregular.columnDegree (fiberMatrix c side x leftColor rightColor edgeColor) rightPoint
  mixed : ∃ u w, fiberMatrix c side x leftColor rightColor edgeColor u rightPoint = true ∧
    fiberMatrix c side x leftColor rightColor edgeColor w rightPoint = false
  twinBound : ∀ u, 2 * (Semiregular.twins (fiberMatrix c side x leftColor rightColor edgeColor) u).card ≤
    rowValency c side leftColor x
  sideSum : rowValency c side leftColor x + rowValency c side rightColor x ≤ n
  disjoint : Disjoint (colorClass c side x leftColor) (colorClass c side x rightColor)
  area : (rowValency c side leftColor x : ℝ) * rowValency c side rightColor x ≤
    eta * (1 - eta) * (n : ℝ) ^ 2

theorem rectangleCertificate_of_dominant (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    (hp : PrimitiveColorCuts c side) (x : Fin n) (i : Color n) (eta : ℝ)
    (heta : (1 / 2 : ℝ) ≤ eta) (hdom : eta * n < (rowValency c side i x : ℝ)) :
    Nonempty (RectangleCertificate c side x eta) := by
  have hhalf := mul_le_mul_of_nonneg_right heta (show (0 : ℝ) ≤ n by positivity)
  have hnreal : (n : ℝ) < 2 * rowValency c side i x := by linarith
  have hi : n < 2 * rowValency c side i x := by exact_mod_cast hnreal
  obtain ⟨a, hxa⟩ := dominant_offDiagonal_witness c hc side hn x i hi
  obtain ⟨j, hji, hjdiag, b, k, rows, columns, mixed, twins, hsum, hdis⟩ :=
    dominant_rectangle_output c hc side hh hn hp x i hi a hxa
  have hidiag : i ≠ c (side, x, x) := by
    intro he
    exact offDiagonal_loop_ne c hc side x a.val x hxa (he.symm.trans a.property.symm)
  have hsumreal : (rowValency c side i x : ℝ) + rowValency c side j x ≤ n := by
    exact_mod_cast hsum
  have harea := GI.rectangle_area_bound (show (0 : ℝ) ≤ n by positivity)
    heta hdom.le (show (rowValency c side j x : ℝ) ≤ n - rowValency c side i x by linarith)
  exact ⟨⟨i, j, k, a, b, hdom, hji, hidiag, hjdiag, rows, columns,
    mixed, twins, hsum, hdis, harea⟩⟩

/-- Once the source vertex is fixed, every primitive-color configuration
gives either a balanced color partition or an actual physical rectangle. -/
theorem primitive_entrance_alternative (c : Coloring n) (hc : Coherent c)
    (side : Bool) (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    (hp : PrimitiveColorCuts c side) (x : Fin n) (eta : ℝ)
    (heta : (1 / 2 : ℝ) ≤ eta) :
    (∀ i, (rowValency c side i x : ℝ) ≤ eta * n) ∨
      Nonempty (RectangleCertificate c side x eta) := by
  classical
  by_cases h : ∀ i, (rowValency c side i x : ℝ) ≤ eta * n
  · exact Or.inl h
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr (rectangleCertificate_of_dominant c hc side hh hn hp x i eta heta hi)

end GI.CoherentEntrance

#print axioms GI.CoherentEntrance.rectangleCertificate_of_dominant
#print axioms GI.CoherentEntrance.primitive_entrance_alternative
