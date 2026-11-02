import Workspace.MatrixKernel
import Workspace.AlternatingSections

namespace GI.Matrix

variable {L R : Type*} [Fintype L] [Fintype R]

def rightKernelLeft (M : L → R → Bool) : (right M).ker →* rowPermutations M where
  toFun g := ⟨left M g.val, by
    have hm : left M g.val ∈ (right M).ker.map (left M) := ⟨g.val, g.property, rfl⟩
    rw [right_kernel_left_image] at hm
    exact hm⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Fintype L] [Fintype R] in
theorem rightKernelLeft_injective (M : L → R → Bool) :
    Function.Injective (rightKernelLeft M) := by
  intro g h heq
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val heq
  · have hg : g.val.val.2 = 1 := g.property
    have hh : h.val.val.2 = 1 := h.property
    exact hg.trans hh.symm

theorem row_cap (M : L → R → Bool) (b : ℕ)
    (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap (rowPermutations M) b := by
  apply SectionCaps.faithful_family (twinAction M)
  · intro g hg
    apply twinProduct_injective M
    rw [map_one]
    exact funext hg
  · intro x
    simpa only [Fintype.card_coe] using sizes x

/-- The actual matrix group, hence every parity-restricted subgroup and
every projected quotient, has the twin/right-side alternating-section cap. -/
theorem matrix_cap (M : L → R → Bool) (b : ℕ)
    (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap (automorphisms M) (max b (Fintype.card R)) :=
  SectionCaps.extension (right M)
    (SectionCaps.of_injective (rightKernelLeft M) (rightKernelLeft_injective M)
      (row_cap M b sizes)) SectionCaps.permutations

theorem semiregular_cap (M : L → R → Bool) (k d : ℕ)
    (rows : ∀ x, Semiregular.rowDegree M x = k)
    (columns : ∀ y, Semiregular.columnDegree M y = d)
    (edge : ∃ a b, M a b = true) (nonedge : ∃ a b, M a b = false) :
    SectionCaps.Cap (automorphisms M) (max (Fintype.card L / 2) (Fintype.card R)) := by
  apply matrix_cap M
  intro x
  have h := Semiregular.nontrivial_twins_half M k d rows columns edge nonedge x
  omega

theorem projected_subgroup_cap (M : L → R → Bool) (A : Subgroup (automorphisms M))
    (b : ℕ) (sizes : ∀ x, (Semiregular.twins M x).card ≤ b) :
    SectionCaps.Cap ((left M).comp A.subtype).range (max b (Fintype.card R)) :=
  SectionCaps.of_surjective _ (QuotientImage.range_surjective _)
    (SectionCaps.subgroup (matrix_cap M b sizes) A)

end GI.Matrix
