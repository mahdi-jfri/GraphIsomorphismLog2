module

public import Workspace.RectangleSides
public import Workspace.RectangleOutput
public import Workspace.MatrixCaps

@[expose] public section

namespace GI.Rectangle

variable {α : Type*} [Fintype α] [DecidableEq α] {W R : Finset α}
variable [Nonempty W] [Nonempty R]

abbrev ActualMatrixAut (M : W → R → Bool) :=
  TransportOutput.aut (rectangleAction (W := W) (R := R)).range (Function.uncurry M)

/-- The actual source automorphism group returned by the rectangle query
embeds in the side-permutation matrix group used in the cap argument. -/
noncomputable def actualMatrixEmbedding (M : W → R → Bool) :
    ActualMatrixAut M →* Matrix.automorphisms M where
  toFun g := ⟨extractSides g.val, (extractSides_transports M M g.val).mp
    ((TransportOutput.mem_aut _ _ g.val).mp g.property)⟩
  map_one' := Subtype.ext (map_one extractSides)
  map_mul' g h := Subtype.ext (map_mul extractSides g.val h.val)

theorem actualMatrixEmbedding_injective (M : W → R → Bool) :
    Function.Injective (actualMatrixEmbedding M) := by
  intro g h heq
  apply Subtype.ext
  apply extractSides_injective
  exact congrArg Subtype.val heq

theorem actual_matrix_cap (M : W → R → Bool) (b : ℕ)
    (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap (ActualMatrixAut M) (max b R.card) := by
  have h := SectionCaps.of_injective (actualMatrixEmbedding M)
    (actualMatrixEmbedding_injective M) (Matrix.matrix_cap M b sizes)
  simpa only [Fintype.card_coe] using h

theorem actual_semiregular_cap (M : W → R → Bool) (k d : ℕ)
    (rows : ∀ x, Semiregular.rowDegree M x = k)
    (columns : ∀ y, Semiregular.columnDegree M y = d)
    (edge : ∃ a b, M a b = true) (nonedge : ∃ a b, M a b = false) :
    SectionCaps.Cap (ActualMatrixAut M) (max (W.card / 2) R.card) := by
  have h := SectionCaps.of_injective (actualMatrixEmbedding M)
    (actualMatrixEmbedding_injective M) (Matrix.semiregular_cap M k d rows columns edge nonedge)
  simpa only [Fintype.card_coe] using h

/-- The cap applies to the closure of the concrete full-output generators,
not to an unrelated matrix automorphism group. -/
theorem returned_generators_cap (M N : W → R → Bool)
    (s : TransportOutput.Solution (rectangleAction (W := W) (R := R)).range
      (Function.uncurry M) (Function.uncurry N)) (k d : ℕ)
    (rows : ∀ x, Semiregular.rowDegree M x = k)
    (columns : ∀ y, Semiregular.columnDegree M y = d)
    (edge : ∃ a b, M a b = true) (nonedge : ∃ a b, M a b = false) :
    SectionCaps.Cap (Subgroup.closure {g | g ∈ s.generators}) (max (W.card / 2) R.card) := by
  rw [s.generates]
  exact actual_semiregular_cap M k d rows columns edge nonedge

noncomputable def actualLeft (M : W → R → Bool) : ActualMatrixAut M →* Equiv.Perm W :=
  (Matrix.left M).comp (actualMatrixEmbedding M)

theorem actual_left_cap (M : W → R → Bool) (b : ℕ)
    (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap (actualLeft M).range (max b R.card) :=
  SectionCaps.of_surjective _ (QuotientImage.range_surjective _) (actual_matrix_cap M b sizes)

end GI.Rectangle
