module

public import Workspace.Impl.RowPure

@[expose] public section

/-!
# The groups of Theorem A.18 in coordinates

For the row form `RowForm.ofPure` built from pure coordinates `e`, the three groups of
Theorem A.18 are projections to row `0` of blockwise elements of `G|_dom`. An element of
`G|_dom` is *blockwise* if it is `cleanRowPerm e y`, that is `e(b, i) ↦ e(y_i b, i)`.

* `H = K[B]`: the row-`0` parts `y_0` of the blockwise elements (`mem_Hb_ofPure`);
* `N`: those with `y_1 = 1` (`mem_Nb_ofPure`);
* `N*`: those with `y_i = 1` for every `i ≠ 0` (`mem_Nstar_ofPure`).

These are the forms that a program computes: blockwise elements are the kernel of the label
map, and the conditions `y_1 = 1` and `y_i = 1 (i ≠ 0)` are pointwise stabilizers.

The one point that is not a definition is that the other rows of a blockwise element also lie in
`H` (`row_mem_Hb`): conjugating by the pure lift of an even permutation that moves row `0` to
row `r` turns row `r` into row `0` (`conj_pure`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Paper GI.Algorithm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- An even permutation of `Fin q` (`q ≥ 3`) that maps `0` to `r`. -/
theorem exists_alt_zero_to {q : ℕ} (hq : 3 ≤ q) (r : Fin q) :
    ∃ p : alternatingGroup (Fin q), p.val ⟨0, by omega⟩ = r := by
  classical
  by_cases hr : r = ⟨0, by omega⟩
  · exact ⟨1, by simp [hr]⟩
  · -- a third point `t`, different from `0` and `r`
    obtain ⟨t, ht0, htr⟩ : ∃ t : Fin q, t ≠ ⟨0, by omega⟩ ∧ t ≠ r := by
      by_cases h1 : r = ⟨1, by omega⟩
      · exact ⟨⟨2, by omega⟩, by simp [Fin.ext_iff], by rw [h1]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff], fun h => h1 h.symm⟩
    refine ⟨⟨swap ⟨0, by omega⟩ t * swap ⟨0, by omega⟩ r, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Ne.symm ht0), sign_swap (Ne.symm hr)]
      rfl
    · show (swap ⟨0, by omega⟩ t) ((swap ⟨0, by omega⟩ r) ⟨0, by omega⟩) = r
      rw [swap_apply_left, swap_apply_of_ne_of_ne hr (Ne.symm htr)]

section OfPure

variable (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {B : Type} [Fintype B] [DecidableEq B]
  (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e) (b₀ : B)

theorem ofPure_i0 : (RowForm.ofPure hnat hq e hP b₀).i0 = ⟨0, by omega⟩ := rfl

/-- **`H` in coordinates.** `σ ∈ H` exactly when some blockwise element of `G|_dom` acts as `σ`
on row `0`. -/
theorem mem_Hb_ofPure (σ : Perm B) :
    σ ∈ (RowForm.ofPure hnat hq e hP b₀).Hb ↔
      ∃ y : Fin L.q → Perm B, cleanRowPerm e y ∈ S.domGroup ∧ y ⟨0, by omega⟩ = σ := by
  show σ ∈ cleanLocalGroup S.domGroup e ⟨0, by omega⟩ ↔ _
  simp only [cleanLocalGroup, Subgroup.mem_map, Subgroup.mem_comap]
  rfl

/-- **Every row of a blockwise element lies in `H`.** -/
theorem row_mem_Hb (y : Fin L.q → Perm B) (hy : cleanRowPerm e y ∈ S.domGroup) (r : Fin L.q) :
    y r ∈ (RowForm.ofPure hnat hq e hP b₀).Hb := by
  obtain ⟨p, hp⟩ := exists_alt_zero_to (by omega : 3 ≤ L.q) r
  set s := (RowForm.ofPure hnat hq e hP b₀).s
  have hpure := (RowForm.ofPure hnat hq e hP b₀).pure
  have hconj := conj_pure (S := S) e hpure p y
  refine (mem_Hb_ofPure hnat hq e hP b₀ _).2 ⟨fun i => y (p.val i), ?_, by simp only [hp]⟩
  rw [← hconj]
  exact S.domGroup.mul_mem (S.domGroup.mul_mem (S.domGroup.inv_mem (s p).2) hy) (s p).2

/-- **`N` in coordinates.** `σ ∈ N` exactly when some blockwise element of `G|_dom` acts as `σ`
on row `0` and trivially on row `1`. -/
theorem mem_Nb_ofPure (σ : Perm B) :
    σ ∈ (RowForm.ofPure hnat hq e hP b₀).Nb ↔
      ∃ y : Fin L.q → Perm B, cleanRowPerm e y ∈ S.domGroup ∧ y ⟨1, by omega⟩ = 1 ∧
        y ⟨0, by omega⟩ = σ := by
  set F := RowForm.ofPure hnat hq e hP b₀
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨x, hx, hx1, hx0⟩ := (mem_rowKernelImage _ _ _ n).1 hn
    have hxG := ((pureComplementOf hnat e hP b₀).mem_normalRows_iff
      (by rw [Fintype.card_fin]; exact hq) ⟨0, by omega⟩ x).1 hx
    refine ⟨fun r => (x r).val, hxG, ?_, ?_⟩
    · have := congrArg Subtype.val hx1
      exact this
    · have := congrArg Subtype.val hx0
      exact this
  · rintro ⟨y, hy, hy1, hy0⟩
    let x : Fin L.q → F.Hb := fun r => ⟨y r, row_mem_Hb hnat hq e hP b₀ y hy r⟩
    have hx := ((pureComplementOf hnat e hP b₀).mem_normalRows_iff
      (by rw [Fintype.card_fin]; exact hq) ⟨0, by omega⟩ x).2 hy
    refine ⟨x ⟨0, by omega⟩, (mem_rowKernelImage _ _ _ _).2 ⟨x, hx, Subtype.ext hy1, rfl⟩, hy0⟩

/-- **`N*` in coordinates.** `σ ∈ N*` exactly when some blockwise element of `G|_dom` acts as
`σ` on row `0` and trivially on every other row. -/
theorem mem_Nstar_ofPure (σ : Perm B) :
    σ ∈ (RowForm.ofPure hnat hq e hP b₀).Nstar.map (RowForm.ofPure hnat hq e hP b₀).Hb.subtype ↔
      ∃ y : Fin L.q → Perm B, cleanRowPerm e y ∈ S.domGroup ∧
        (∀ r, r ≠ ⟨0, by omega⟩ → y r = 1) ∧ y ⟨0, by omega⟩ = σ := by
  classical
  set F := RowForm.ofPure hnat hq e hP b₀
  have h5 : 5 ≤ Fintype.card (Fin L.q) := by rw [Fintype.card_fin]; exact hq
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hx := (mem_rowSingleKernel _ _ n).1 hn
    have hxG := ((pureComplementOf hnat e hP b₀).mem_normalRows_iff h5 ⟨0, by omega⟩ _).1 hx
    refine ⟨fun r => (rowSingle (⟨0, by omega⟩ : Fin L.q) n r).val, hxG, fun r hr => ?_, ?_⟩
    · simp [rowSingle, hr]; rfl
    · simp [rowSingle]; rfl
  · rintro ⟨y, hy, hy1, hy0⟩
    have h0 : y ⟨0, by omega⟩ ∈ F.Hb := row_mem_Hb hnat hq e hP b₀ y hy _
    refine ⟨⟨y ⟨0, by omega⟩, h0⟩, ?_, hy0⟩
    show rowSingle (⟨0, by omega⟩ : Fin L.q) ⟨y ⟨0, by omega⟩, h0⟩ ∈
      (pureComplementOf hnat e hP b₀).normalRows h5 ⟨0, by omega⟩
    refine ((pureComplementOf hnat e hP b₀).mem_normalRows_iff h5 ⟨0, by omega⟩ _).2 ?_
    have hfun : (fun r => (rowSingle (⟨0, by omega⟩ : Fin L.q)
        (⟨y ⟨0, by omega⟩, h0⟩ : F.Hb) r).val) = y := by
      funext r
      by_cases hr : r = ⟨0, by omega⟩
      · rw [hr]; simp [rowSingle]; rfl
      · simp [rowSingle, hr, hy1 r hr]; rfl
    exact (congrArg (fun z => cleanRowPerm e z ∈ S.domGroup) hfun).mpr hy

end OfPure

/-! ### Row-preserving elements and their row-`0` part

A program computes generators, not membership tests. The generators of `H`, `N`, `N*` are
the row-`0` parts of generators of three subgroups of `G|_dom` that preserve every row. Taking
the row-`0` part is a homomorphism on row-preserving permutations (`rowPart`), so it maps a
generating set of such a subgroup onto a generating set of the image (`closure_rowPart`). -/

section RowPart

variable {V B : Type} {q : ℕ} (e : B × Fin q ≃ V)

theorem apply_of_row {g : Perm V} (hg : ∀ b i, (e.symm (g (e (b, i)))).2 = i) (b : B)
    (i : Fin q) : g (e (b, i)) = e ((e.symm (g (e (b, i)))).1, i) := by
  conv_lhs => rw [← e.apply_symm_apply (g (e (b, i)))]
  congr 1
  exact Prod.ext rfl (hg b i)

/-- The permutations that map every row `B × {i}` to itself. -/
def rowPres : Subgroup (Perm V) where
  carrier := {g | ∀ b i, (e.symm (g (e (b, i)))).2 = i}
  one_mem' b i := by simp
  mul_mem' {g h} hg hh b i := by
    show (e.symm (g (h (e (b, i))))).2 = i
    rw [apply_of_row e hh b i]
    exact hg _ _
  inv_mem' {g} hg b i := by
    show (e.symm (g⁻¹ (e (b, i)))).2 = i
    obtain ⟨⟨c, j⟩, hc⟩ := e.surjective (g⁻¹ (e (b, i)))
    have : g (e (c, j)) = e (b, i) := by rw [hc, Perm.apply_inv_self]
    have hj := hg c j
    rw [this, e.symm_apply_apply] at hj
    rw [← hc, e.symm_apply_apply]
    exact hj.symm

theorem rowPres_apply {g : Perm V} (hg : g ∈ rowPres e) (b : B) (i : Fin q) :
    g (e (b, i)) = e ((e.symm (g (e (b, i)))).1, i) :=
  apply_of_row e hg b i

/-- The action of a row-preserving permutation on row `i`. -/
def rowPartFun (i : Fin q) (g : Perm V) (b : B) : B := (e.symm (g (e (b, i)))).1

theorem rowPartFun_mul {g h : Perm V} (hh : h ∈ rowPres e) (i : Fin q) (b : B) :
    rowPartFun e i (g * h) b = rowPartFun e i g (rowPartFun e i h b) := by
  simp only [rowPartFun, Perm.mul_apply]
  rw [rowPres_apply e hh b i, e.symm_apply_apply]

/-- **The row-`i` part**, a homomorphism on row-preserving permutations. -/
def rowPart (i : Fin q) : rowPres e →* Perm B where
  toFun g :=
    { toFun := rowPartFun e i g.val
      invFun := rowPartFun e i g.val⁻¹
      left_inv := fun b => by
        rw [← rowPartFun_mul e g.2, inv_mul_cancel]
        simp [rowPartFun]
      right_inv := fun b => by
        rw [← rowPartFun_mul e ((rowPres e).inv_mem g.2), mul_inv_cancel]
        simp [rowPartFun] }
  map_one' := by ext b; simp [rowPartFun]
  map_mul' g h := by
    ext b
    exact rowPartFun_mul e h.2 i b

theorem rowPart_apply (i : Fin q) (g : rowPres e) (b : B) :
    rowPart e i g b = (e.symm (g.val (e (b, i)))).1 := rfl

theorem cleanRowPerm_mem_rowPres (y : Fin q → Perm B) : cleanRowPerm e y ∈ rowPres e := by
  intro b i
  rw [cleanRowPerm_apply, e.symm_apply_apply]

theorem rowPart_cleanRowPerm (y : Fin q → Perm B) (i : Fin q) :
    rowPart e i ⟨_, cleanRowPerm_mem_rowPres e y⟩ = y i := by
  ext b
  rw [rowPart_apply, cleanRowPerm_apply, e.symm_apply_apply]

/-- Every row-preserving permutation is blockwise. -/
theorem eq_cleanRowPerm (g : rowPres e) :
    g.val = cleanRowPerm e (fun i => rowPart e i g) := by
  ext v
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
  rw [cleanRowPerm_apply, rowPart_apply, rowPres_apply e g.2 b i, e.symm_apply_apply]

/-- **Generators of the row-`i` image.** If `gs ⊆ rowPres e` generate `A`, then their row-`i`
parts generate the row-`i` parts of `A`. -/
theorem closure_rowPart (i : Fin q) (A : Subgroup (Perm V)) (hA : A ≤ rowPres e)
    (gs : List (Perm V)) (hgs : Subgroup.closure {g | g ∈ gs} = A) :
    Subgroup.closure {σ | ∃ g, ∃ hg : g ∈ gs, σ = rowPart e i ⟨g, hA (hgs ▸ Subgroup.subset_closure hg)⟩} =
      (A.subgroupOf (rowPres e)).map (rowPart e i) := by
  have hcl : A.subgroupOf (rowPres e) =
      Subgroup.closure {x : rowPres e | x.val ∈ gs} := by
    rw [← hgs]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have : x.val ∈ (Subgroup.closure {x : rowPres e | x.val ∈ gs}).map (rowPres e).subtype := by
        rw [MonoidHom.map_closure]
        refine (Subgroup.closure_mono ?_) hx
        intro g hg
        exact ⟨⟨g, hA (hgs ▸ Subgroup.subset_closure hg)⟩, hg, rfl⟩
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← Subtype.ext hyx]
    · rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure hx
  rw [hcl, MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, _⟩, hg, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩

end RowPart

/-- The permutations that fix every point of a set. -/
def fixSet {V : Type} (X : Set V) : Subgroup (Perm V) where
  carrier := {g | ∀ x ∈ X, g x = x}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x hx := by
    show g (h x) = x
    rw [hh x hx, hg x hx]
  inv_mem' {g} hg x hx := by
    show g⁻¹ x = x
    rw [Perm.inv_eq_iff_eq, hg x hx]

/-- The points of row `i`. -/
def rowSet {V B : Type} {q : ℕ} (e : B × Fin q ≃ V) (i : Fin q) : Set V := {v | (e.symm v).2 = i}

/-- An element fixing every point outside row `i` maps row `i` to itself, so it preserves all
rows. -/
theorem fixSet_compl_le {V B : Type} {q : ℕ} (e : B × Fin q ≃ V) (i : Fin q) :
    fixSet (rowSet e i)ᶜ ≤ rowPres e := by
  intro g hg b j
  by_cases hj : j = i
  · -- the image of a row-`i` point is in row `i`: otherwise it is a fixed point
    subst hj
    by_contra hne
    have hout : g (e (b, j)) ∈ (rowSet e j)ᶜ := hne
    have hfix := hg _ hout
    have := g.injective hfix
    rw [this, e.symm_apply_apply] at hne
    exact hne rfl
  · have hin : e (b, j) ∈ (rowSet e i)ᶜ := by
      show ¬ (e.symm (e (b, j))).2 = i
      rw [e.symm_apply_apply]; exact hj
    rw [hg _ hin, e.symm_apply_apply]

section OfPureGroups

variable (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {B : Type} [Fintype B] [DecidableEq B]
  (e : B × Fin L.q ≃ S.dom) (hP : PureCoords S L label e) (b₀ : B)

/-- **`H` as an image**: the row-`0` parts of the row-preserving elements of `G|_dom`. -/
theorem Hb_eq_rowPart : (RowForm.ofPure hnat hq e hP b₀).Hb =
    ((S.domGroup ⊓ rowPres e).subgroupOf (rowPres e)).map (rowPart e ⟨0, by omega⟩) := by
  ext (σ : Perm B)
  refine (mem_Hb_ofPure hnat hq e hP b₀ σ).trans ?_
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨_, cleanRowPerm_mem_rowPres e y⟩,
      Subgroup.mem_subgroupOf.2 ⟨hy, cleanRowPerm_mem_rowPres e y⟩, rowPart_cleanRowPerm e y _⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun i => rowPart e i g, ?_, rfl⟩
    rw [← eq_cleanRowPerm]
    exact (Subgroup.mem_subgroupOf.1 hg).1

/-- **`N` as an image**: the row-`0` parts of the row-preserving elements of `G|_dom` that fix
row `1` pointwise. -/
theorem Nb_eq_rowPart : (RowForm.ofPure hnat hq e hP b₀).Nb =
    ((S.domGroup ⊓ rowPres e ⊓ fixSet (rowSet e ⟨1, by omega⟩)).subgroupOf (rowPres e)).map
      (rowPart e ⟨0, by omega⟩) := by
  ext (σ : Perm B)
  refine (mem_Nb_ofPure hnat hq e hP b₀ σ).trans ?_
  constructor
  · rintro ⟨y, hy, hy1, rfl⟩
    refine ⟨⟨_, cleanRowPerm_mem_rowPres e y⟩, Subgroup.mem_subgroupOf.2
      ⟨⟨hy, cleanRowPerm_mem_rowPres e y⟩, ?_⟩, rowPart_cleanRowPerm e y _⟩
    intro v hv
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
    have hi : i = ⟨1, by omega⟩ := by simpa [rowSet] using hv
    rw [cleanRowPerm_apply, hi, hy1]
    rfl
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨⟨hG, -⟩, hfix⟩ := Subgroup.mem_subgroupOf.1 hg
    refine ⟨fun i => rowPart e i g, ?_, ?_, rfl⟩
    · rw [← eq_cleanRowPerm]; exact hG
    · ext b
      rw [rowPart_apply, hfix (e (b, ⟨1, by omega⟩)) (by simp [rowSet]), e.symm_apply_apply]
      rfl

/-- **`N*` as an image**: the row-`0` parts of the elements of `G|_dom` that fix every point
outside row `0`. -/
theorem Nstar_eq_rowPart : (RowForm.ofPure hnat hq e hP b₀).Nstar.map
      (RowForm.ofPure hnat hq e hP b₀).Hb.subtype =
    ((S.domGroup ⊓ fixSet (rowSet e ⟨0, by omega⟩)ᶜ).subgroupOf (rowPres e)).map
      (rowPart e ⟨0, by omega⟩) := by
  ext (σ : Perm B)
  refine (mem_Nstar_ofPure hnat hq e hP b₀ σ).trans ?_
  constructor
  · rintro ⟨y, hy, hy1, rfl⟩
    refine ⟨⟨_, cleanRowPerm_mem_rowPres e y⟩, Subgroup.mem_subgroupOf.2 ⟨hy, ?_⟩,
      rowPart_cleanRowPerm e y _⟩
    intro v hv
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective v
    have hi : i ≠ ⟨0, by omega⟩ := by simpa [rowSet] using hv
    rw [cleanRowPerm_apply, hy1 i hi]
    rfl
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hG, hfix⟩ := Subgroup.mem_subgroupOf.1 hg
    refine ⟨fun i => rowPart e i g, ?_, fun r hr => ?_, rfl⟩
    · rw [← eq_cleanRowPerm]; exact hG
    · ext b
      rw [rowPart_apply, hfix (e (b, r)) (by simpa [rowSet] using hr), e.symm_apply_apply]
      rfl

end OfPureGroups

end GI.Impl
