import Workspace.Algorithm.RowFormOf

/-!
# Pure coordinates give the row normal form

Theorem A.17 asks for coordinates `e : B × [m] ≃ dom`, with block `i` equal to `B × {i}`, and a
clean complement `R = s(Alt(m))` that acts only on the block index. The program computes the
coordinates first. This file shows that the rest of the data of `RowForm` then follows, with no
cited input:

* **the purity criterion** (`PureCoords`): if every *pure* even permutation
  `e(b, i) ↦ e(b, p i)` lies in `G|_dom`, then these permutations form a clean complement of
  the block kernel (`CleanBlockAction.cleanRange_isComplement`: a pure permutation with trivial
  top is the identity, and the pure permutations map onto the top);
* the row normal form of Theorem A.18 is a consequence of a pure complement
  (`PureComplement.isRowNormalForm`), for `m ≥ 5`.

So `RowForm.ofPure` builds a `RowForm` whose coordinates are exactly the given `e`.

To check purity, it is enough to check it on generators of `Alt(m)`. We use the 3-cycles
`(0 1 2)` and `(0 j 1)` for `j ≥ 3` (`pureCoords_of_gen`): they generate `Alt(m)`, since every
product `(0 a)(0 b)` of two transpositions through `0` is a product of them
(`alternating_le_of_root_pairs`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Paper GI.Algorithm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- **Pure coordinates**: block `i` is `B × {i}`, and every pure even permutation lies in
`G|_dom`. -/
structure PureCoords (S : State Ω C) (L : GiantLabels S) (label : Ω → Fin L.q) {B : Type}
    (e : B × Fin L.q ≃ S.dom) : Prop where
  label_e : ∀ b i, label (e (b, i)) = i
  mem : ∀ p : alternatingGroup (Fin L.q), coordinatePureLift e p.val ∈ S.domGroup

/-- The block action of `G|_dom` on the natural row labels. -/
noncomputable def rowAction (hnat : NaturalRows S L label) :
    CleanBlockAction S.domGroup (Fin L.q) where
  label v := label v
  label_surjective i := by
    obtain ⟨v, hv, h⟩ := hnat.onto i
    exact ⟨⟨v, hv⟩, h⟩
  top := topHom hnat
  top_surjective := topHom_surjective hnat
  action := topHom_equivariant hnat

theorem rowAction_ker (hnat : NaturalRows S L label) {B : Type} (e : B × Fin L.q ≃ S.dom)
    (he : ∀ b i, label (e (b, i)) = i) : (rowAction hnat).top.ker = blockKernel e := by
  rw [← ker_eq_blockKernel hnat e he]
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
    OneMemClass.coe_eq_one]
  rfl

/-- **The pure complement of pure coordinates.** -/
noncomputable def pureComplementOf (hnat : NaturalRows S L label) {B : Type}
    (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e) (b₀ : B) :
    PureComplement (rowAction hnat) where
  Fiber := B
  base := b₀
  coordinates := e
  sectionHom := CleanBlockAction.cleanSection (G := S.domGroup) e hP.mem
  label_coordinates := hP.label_e
  pure p b i := coordinatePureLift_apply e p.val b i
  top_section := (rowAction hnat).top_cleanSection e b₀ hP.label_e hP.mem
  isComplement := (rowAction hnat).cleanRange_isComplement e b₀ hP.label_e hP.mem

/-- The second row used to define `N` in Theorem A.18. -/
def otherRow (q : ℕ) (h : 2 ≤ q) : Fin q := ⟨1, by omega⟩

theorem otherRow_ne (q : ℕ) (h : 2 ≤ q) : otherRow q h ≠ ⟨0, by omega⟩ := by
  simp [otherRow, Fin.ext_iff]

/-- **The row normal form from pure coordinates** (Theorems A.17 and A.18). The coordinates of
the result are `e` (`ofPure_e`). The block `i0` of A.18 is `0`. -/
noncomputable def RowForm.ofPure (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {B : Type}
    [Fintype B] [DecidableEq B] (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e)
    (b₀ : B) : RowForm S L :=
  have h5 : 5 ≤ Fintype.card (Fin L.q) := by rw [Fintype.card_fin]; exact hq
  let c := pureComplementOf hnat e hP b₀
  let i0 : Fin L.q := ⟨0, by omega⟩
  let i1 : Fin L.q := otherRow L.q (by omega)
  have hrnf := c.isRowNormalForm h5 i0 (otherRow_ne L.q (by omega))
  { B := B
    label := label
    natural := hnat
    e := e
    e_label := hP.label_e
    four_le := by omega
    s := c.sectionHom
    pure := c.pure
    complement := by
      have := c.isComplement
      rwa [rowAction_ker hnat e hP.label_e] at this
    i0 := i0
    Nl := c.rowN h5 i0 (i := i1)
    Nstar := c.rowNstar h5 i0
    Nl_normal := PureComplement.rowN_normal c h5 i0 (i := i1)
    Nstar_normal := PureComplement.rowNstar_normal c h5 i0
    rnf := by
      have := hrnf
      rwa [rowAction_ker hnat e hP.label_e] at this }

theorem RowForm.ofPure_e (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {B : Type}
    [Fintype B] [DecidableEq B] (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e)
    (b₀ : B) : (RowForm.ofPure hnat hq e hP b₀).e = e := rfl

theorem RowForm.ofPure_label (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {B : Type}
    [Fintype B] [DecidableEq B] (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e)
    (b₀ : B) : (RowForm.ofPure hnat hq e hP b₀).label = label := rfl

/-! ### Purity from generators -/

/-- The 3-cycles `(0 1 2)` and `(0 j 1)` for `j ≥ 3` generate `Alt(q)`. -/
theorem alternating_le_of_gen {q : ℕ} (hq : 3 ≤ q) (K : Subgroup (Perm (Fin q)))
    (h12 : cleanCycle (⟨0, by omega⟩ : Fin q) ⟨1, by omega⟩ ⟨2, by omega⟩ ∈ K)
    (hj : ∀ j : Fin q, 3 ≤ (j : ℕ) → cleanCycle (⟨0, by omega⟩ : Fin q) j ⟨1, by omega⟩ ∈ K) :
    alternatingGroup (Fin q) ≤ K := by
  set o : Fin q := ⟨0, by omega⟩
  set u : Fin q := ⟨1, by omega⟩
  -- `(0 a)(0 1) ∈ K` and `(0 1)(0 b) ∈ K` for all `a, b ≠ 0`.
  have hl : ∀ a : Fin q, a ≠ o → swap o a * swap o u ∈ K := by
    intro a ha
    by_cases h1 : a = u
    · subst h1; simp
    by_cases h2 : (a : ℕ) = 2
    · have : a = ⟨2, by omega⟩ := Fin.ext h2
      rw [this]
      exact h12
    · have h3 : 3 ≤ (a : ℕ) := by
        have : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
        have : (a : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
        omega
      have := K.inv_mem (hj a h3)
      simpa [cleanCycle, mul_inv_rev] using this
  have hr : ∀ b : Fin q, b ≠ o → swap o u * swap o b ∈ K := by
    intro b hb
    have := K.inv_mem (hl b hb)
    simpa [mul_inv_rev] using this
  refine alternating_le_of_root_pairs K o fun a b ha hb => ?_
  have := K.mul_mem (hl a ha) (hr b hb)
  simpa [mul_assoc] using this

/-- **Purity from the generators**: if the pure 3-cycles `(0 1 2)` and `(0 j 1)` lie in
`G|_dom`, then every pure even permutation does. -/
theorem pureMem_of_gen {B : Type} (e : B × Fin L.q ≃ S.dom) (hq : 3 ≤ L.q)
    (h12 : coordinatePureLift e (cleanCycle ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩) ∈
      S.domGroup)
    (hj : ∀ j : Fin L.q, 3 ≤ (j : ℕ) →
      coordinatePureLift e (cleanCycle ⟨0, by omega⟩ j ⟨1, by omega⟩) ∈ S.domGroup)
    (p : alternatingGroup (Fin L.q)) : coordinatePureLift e p.val ∈ S.domGroup :=
  alternating_le_of_gen hq (S.domGroup.comap (coordinatePureLift e)) h12 hj p.2

end GI.Impl
