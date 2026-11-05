module

public import Workspace.RectangleSides

@[expose] public section

/-!
# The exact side image of the permitted group, parity twists and alignments

`P = (Sym W × Sym R × Sym Y) ∩ Alt Γ` is `GI.Rectangle.permitted W R`, with
`Y = Γ \ (W ∪ R)`. Its image in `Sym W × Sym R` (`sideAction`) is

* the pairs of even total parity when `|Y| ≤ 1` (`sideAction_mem_range_iff`),
* all of `Sym W × Sym R` when `|Y| ≥ 2` (`sideAction_range_eq_top`).

This is the image claimed in Lemma A.30 and in the paragraph "Parity and
source--target alignment" after Lemma A.27. With `R = Γ \ W` (so `Y = ∅`) it gives
the index bound `[H : H₀] ≤ 2` of Lemma A.11 (`evenSides_relIndex_le_two`) and its
second coset (`twist_not_mem_evenSides`, `mem_evenSides_or_twist`).

The alignment of source and target sides by an even permutation
(`exists_even_alignment`) and the alignment coset (`alignment_coset`) are the
first part of the paragraph "Parity and source--target alignment".
-/

namespace GI.Rectangle

open Equiv Equiv.Perm
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α] {W R : Finset α}

/-! ### Assembling a permutation from its two sides -/

/-- The permutation acting as `σ` on `W`, as `τ` on `R`, and trivially elsewhere. -/
def sidePerm (σ : Perm W) (τ : Perm R) : Perm α := ofSubtype σ * ofSubtype τ

omit [Fintype α] in
theorem sidePerm_apply_left (hd : Disjoint W R) (σ : Perm W) (τ : Perm R) {a : α}
    (ha : a ∈ W) : sidePerm σ τ a = σ ⟨a, ha⟩ := by
  have haR : a ∉ R := fun h => Finset.disjoint_left.mp hd ha h
  change ofSubtype σ (ofSubtype τ a) = _
  rw [ofSubtype_apply_of_not_mem τ haR, ofSubtype_apply_of_mem σ ha]

omit [Fintype α] in
theorem sidePerm_apply_right (hd : Disjoint W R) (σ : Perm W) (τ : Perm R) {a : α}
    (ha : a ∈ R) : sidePerm σ τ a = τ ⟨a, ha⟩ := by
  have h1 : ((τ ⟨a, ha⟩ : R) : α) ∉ W :=
    fun hw => Finset.disjoint_left.mp hd hw (τ ⟨a, ha⟩).property
  change ofSubtype σ (ofSubtype τ a) = _
  rw [ofSubtype_apply_of_mem τ ha, ofSubtype_apply_of_not_mem σ h1]

omit [Fintype α] in
theorem sidePerm_apply_out (σ : Perm W) (τ : Perm R) {a : α} (haW : a ∉ W) (haR : a ∉ R) :
    sidePerm σ τ a = a := by
  change ofSubtype σ (ofSubtype τ a) = _
  rw [ofSubtype_apply_of_not_mem τ haR, ofSubtype_apply_of_not_mem σ haW]

theorem sign_sidePerm (σ : Perm W) (τ : Perm R) :
    sign (sidePerm σ τ) = sign σ * sign τ := by
  rw [sidePerm, Perm.sign_mul, sign_ofSubtype, sign_ofSubtype]

omit [Fintype α] [DecidableEq α] in
/-- A permutation that maps `W` into `W` and `R` into `R` fixes both setwise. -/
theorem mem_sides_of_maps (p : Perm α) (hW : ∀ a ∈ W, p a ∈ W) (hR : ∀ a ∈ R, p a ∈ R) :
    p ∈ sides W R := by
  have key : ∀ S : Finset α, (∀ a ∈ S, p a ∈ S) →
      p ∈ MulAction.stabilizer (Perm α) (S : Set α) := by
    intro S hS
    have hsub : S.map p.toEmbedding ⊆ S := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact hS a ha
    have heq : S.map p.toEmbedding = S :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map])
    rw [MulAction.mem_stabilizer_iff]
    ext b
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hS a ha
    · intro hb
      have hb' : b ∈ S.map p.toEmbedding := by rw [heq]; exact hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb'
      exact ⟨a, ha, rfl⟩
  exact ⟨key W hW, key R hR⟩

omit [Fintype α] [DecidableEq α] in
/-- A permutation fixing `W ∪ R` pointwise lies in `sides W R`. -/
theorem mem_sides_of_fixes (e : Perm α) (he : ∀ a, a ∈ W ∨ a ∈ R → e a = a) :
    e ∈ sides W R :=
  mem_sides_of_maps e (fun a ha => by rw [he a (Or.inl ha)]; exact ha)
    (fun a ha => by rw [he a (Or.inr ha)]; exact ha)

omit [Fintype α] in
theorem sidePerm_mem_sides (hd : Disjoint W R) (σ : Perm W) (τ : Perm R) :
    sidePerm σ τ ∈ sides W R :=
  mem_sides_of_maps _ (fun a ha => by rw [sidePerm_apply_left hd σ τ ha]; exact Subtype.property _)
    (fun a ha => by rw [sidePerm_apply_right hd σ τ ha]; exact Subtype.property _)

/-- If `e` fixes `W ∪ R` pointwise and `sign σ · sign τ · sign e = 1`, then
`sidePerm σ τ * e` is a permitted permutation with side permutations `(σ, τ)`. -/
theorem exists_sideAction_of_fixes (hd : Disjoint W R) (σ : Perm W) (τ : Perm R) (e : Perm α)
    (he : ∀ a, a ∈ W ∨ a ∈ R → e a = a) (hsign : sign σ * sign τ * sign e = 1) :
    ∃ g : permitted W R, sideAction g = (σ, τ) := by
  have hmem : sidePerm σ τ * e ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_sidePerm, hsign]
  have hside : sidePerm σ τ * e ∈ sides W R :=
    (sides W R).mul_mem (sidePerm_mem_sides hd σ τ) (mem_sides_of_fixes e he)
  refine ⟨⟨⟨_, hmem⟩, hside⟩, Prod.ext (Equiv.ext fun a => Subtype.ext ?_)
    (Equiv.ext fun a => Subtype.ext ?_)⟩
  · change sidePerm σ τ (e a.val) = (σ a).val
    rw [he a.val (Or.inl a.property), sidePerm_apply_left hd σ τ a.property]
  · change sidePerm σ τ (e a.val) = (τ a).val
    rw [he a.val (Or.inr a.property), sidePerm_apply_right hd σ τ a.property]

/-- A permitted permutation agrees on `W ∪ R` with the permutation assembled from its
two sides. -/
theorem sidePerm_sideAction_apply (hd : Disjoint W R) (g : permitted W R) {a : α}
    (ha : a ∈ W ∨ a ∈ R) :
    sidePerm (sideAction g).1 (sideAction g).2 a = ((g : alternatingGroup α) : Perm α) a := by
  rcases ha with ha | ha
  · rw [sidePerm_apply_left hd _ _ ha]; rfl
  · rw [sidePerm_apply_right hd _ _ ha]; rfl

/-- A permutation that moves at most one point is the identity. -/
theorem eq_one_of_fixes_compl (e : Perm α) (S : Finset α) (hS : Sᶜ.card ≤ 1)
    (he : ∀ a ∈ S, e a = a) : e = 1 := by
  have hsub : e.support ⊆ Sᶜ := by
    intro a ha
    rw [Finset.mem_compl]
    intro haS
    exact (Perm.mem_support.mp ha) (he a haS)
  have hcard : e.support.card ≤ 1 := (Finset.card_le_card hsub).trans hS
  have h0 : e.support.card = 0 := by
    have := card_support_ne_one e
    omega
  exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)

/-! ### The exact side image -/

/-- When `|Y| ≤ 1`, every permitted permutation has side permutations of even total
parity: the permutation agrees with `sidePerm σ τ` on `W ∪ R`, and the quotient of
the two moves at most the one point of `Y`, so it is trivial. -/
theorem sideAction_sign (hd : Disjoint W R) (hY : (W ∪ R)ᶜ.card ≤ 1) (g : permitted W R) :
    sign (sideAction g).1 * sign (sideAction g).2 = 1 := by
  set k := sidePerm (sideAction g).1 (sideAction g).2
  have hfix : ∀ a ∈ W ∪ R, (k⁻¹ * ((g : alternatingGroup α) : Perm α)) a = a := by
    intro a ha
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
    exact (sidePerm_sideAction_apply hd g (Finset.mem_union.mp ha)).symm
  have he := eq_one_of_fixes_compl _ (W ∪ R) hY hfix
  have hg : ((g : alternatingGroup α) : Perm α) = k := by
    rw [inv_mul_eq_one] at he
    exact he.symm
  have hsg : sign ((g : alternatingGroup α) : Perm α) = 1 := (g : alternatingGroup α).property
  rw [hg, sign_sidePerm] at hsg
  exact hsg

/-- Every pair of side permutations of even total parity is the side image of a
permitted permutation (it acts as `σ` on `W`, `τ` on `R`, trivially elsewhere). -/
theorem exists_sideAction_of_even (hd : Disjoint W R) (σ : Perm W) (τ : Perm R)
    (h : sign σ * sign τ = 1) : ∃ g : permitted W R, sideAction g = (σ, τ) :=
  exists_sideAction_of_fixes hd σ τ 1 (fun _ _ => rfl) (by rw [sign_one, mul_one, h])

/-- When `|Y| ≥ 2`, every pair of side permutations is a side image: "a sign can be
corrected on `Y`" by a transposition of two points of `Y`. -/
theorem exists_sideAction_of_two (hd : Disjoint W R) (hY : 2 ≤ (W ∪ R)ᶜ.card)
    (σ : Perm W) (τ : Perm R) : ∃ g : permitted W R, sideAction g = (σ, τ) := by
  by_cases h : sign σ * sign τ = 1
  · exact exists_sideAction_of_even hd σ τ h
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp (by omega : 1 < (W ∪ R)ᶜ.card)
  rw [Finset.mem_compl, Finset.mem_union, not_or] at hy hz
  refine exists_sideAction_of_fixes hd σ τ (swap y z) (fun a ha => ?_) ?_
  · have hay : a ≠ y := by rintro rfl; rcases ha with ha | ha; exacts [hy.1 ha, hy.2 ha]
    have haz : a ≠ z := by rintro rfl; rcases ha with ha | ha; exacts [hz.1 ha, hz.2 ha]
    exact swap_apply_of_ne_of_ne hay haz
  · rw [sign_swap hyz]
    rcases Int.units_eq_one_or (sign σ * sign τ) with h' | h'
    · exact absurd h' h
    · rw [h']; rfl

/-- **The ideal image when `|Y| ≤ 1`**: exactly the pairs of even total parity. -/
theorem sideAction_mem_range_iff (hd : Disjoint W R) (hY : (W ∪ R)ᶜ.card ≤ 1)
    (p : Perm W × Perm R) :
    p ∈ (sideAction (W := W) (R := R)).range ↔ sign p.1 * sign p.2 = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact sideAction_sign hd hY g
  · intro h
    obtain ⟨g, hg⟩ := exists_sideAction_of_even hd p.1 p.2 h
    exact ⟨g, hg⟩

/-- **The ideal image when `|Y| ≥ 2`**: all of `Sym W × Sym R`. -/
theorem sideAction_range_eq_top (hd : Disjoint W R) (hY : 2 ≤ (W ∪ R)ᶜ.card) :
    (sideAction (W := W) (R := R)).range = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨σ, τ⟩ -
  obtain ⟨g, hg⟩ := exists_sideAction_of_two hd hY σ τ
  exact ⟨g, hg⟩

/-- Two permitted permutations have the same side image exactly when they differ by
an element of the pointwise `(W ∪ R)`-stabilizer: "The full ideal transporter ... is
obtained from the projected lifts by adjoining the pointwise `(W ∪ R)`-stabilizer in
the alternating group." -/
theorem sideAction_eq_iff (g h : permitted W R) :
    sideAction g = sideAction h ↔
      ∀ a, a ∈ W ∨ a ∈ R →
        (((g⁻¹ * h : permitted W R) : alternatingGroup α) : Perm α) a = a := by
  constructor
  · intro hgh a ha
    have e : ((h : alternatingGroup α) : Perm α) a = ((g : alternatingGroup α) : Perm α) a := by
      rcases ha with ha | ha
      · exact congrArg Subtype.val (congrArg (fun p => p.1 ⟨a, ha⟩) hgh.symm)
      · exact congrArg Subtype.val (congrArg (fun p => p.2 ⟨a, ha⟩) hgh.symm)
    change ((g : alternatingGroup α) : Perm α)⁻¹ (((h : alternatingGroup α) : Perm α) a) = a
    rw [e, Perm.inv_apply_self]
  · intro hfix
    have e : ∀ a, a ∈ W ∨ a ∈ R →
        ((h : alternatingGroup α) : Perm α) a = ((g : alternatingGroup α) : Perm α) a := by
      intro a ha
      have := hfix a ha
      change ((g : alternatingGroup α) : Perm α)⁻¹ (((h : alternatingGroup α) : Perm α) a) = a
        at this
      rw [Perm.inv_eq_iff_eq] at this
      exact this
    refine Prod.ext (Equiv.ext fun a => Subtype.ext ?_) (Equiv.ext fun a => Subtype.ext ?_)
    · exact (e a.val (Or.inl a.property)).symm
    · exact (e a.val (Or.inr a.property)).symm

/-! ### The even subgroup `Alt(W) × Alt(R)` and its index (Lemma A.11) -/

/-- The signs of the two side permutations. -/
def sideSigns (W R : Finset α) : permitted W R →* ℤˣ × ℤˣ :=
  (MonoidHom.prodMap sign sign).comp sideAction

/-- `(Alt W × Alt R)`, inside `Alt Γ`: permitted permutations both of whose sides are
even. -/
def evenSides (W R : Finset α) : Subgroup (alternatingGroup α) :=
  (sideSigns W R).ker.map (permitted W R).subtype

theorem mem_evenSides_iff (g : alternatingGroup α) :
    g ∈ evenSides W R ↔ ∃ h : g ∈ permitted W R,
      sign (sideAction ⟨g, h⟩).1 = 1 ∧ sign (sideAction ⟨g, h⟩).2 = 1 := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    have h := (MonoidHom.mem_ker).mp hg'
    exact ⟨g'.property, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨⟨g, h⟩, (MonoidHom.mem_ker).mpr (Prod.ext h1 h2), rfl⟩

theorem evenSides_le : evenSides W R ≤ permitted W R := by
  rintro _ ⟨g, -, rfl⟩
  exact g.property

/-- When `R = Γ \ W`, a permitted permutation is in `Alt(W) × Alt(R)` exactly when its
`W`-side is even. -/
theorem mem_evenSides_compl_iff (W : Finset α) (g : permitted W Wᶜ) :
    (g : alternatingGroup α) ∈ evenSides W Wᶜ ↔ sign (sideAction g).1 = 1 := by
  have hY : (W ∪ Wᶜ)ᶜ.card ≤ 1 := by simp
  have hs := sideAction_sign disjoint_compl_right hY g
  rw [mem_evenSides_iff]
  constructor
  · rintro ⟨_, h1, -⟩
    exact h1
  · intro h1
    refine ⟨g.property, h1, ?_⟩
    rw [h1, one_mul] at hs
    exact hs

/-- **`[P : Alt(W) × Alt(Γ \ W)] ≤ 2`**: inside the permitted group, `Alt(W) × Alt(C)` is
the kernel of the sign of the `W`-side, a homomorphism into `{±1}`. -/
theorem evenSides_relIndex_le_two (W : Finset α) :
    (evenSides W Wᶜ).relIndex (permitted W Wᶜ) ≤ 2 := by
  let f : permitted W Wᶜ →* ℤˣ := sign.comp ((MonoidHom.fst _ _).comp sideAction)
  have hker : (evenSides W Wᶜ).subgroupOf (permitted W Wᶜ) = f.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_evenSides_compl_iff]
    rfl
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  calc Nat.card f.range ≤ Nat.card ℤˣ := Finite.card_subtype_le _
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- The paired transposition `(a b)(c d)`, with `a, b ∈ W` and `c, d ∉ W`, is even,
permitted, and not in `Alt(W) × Alt(C)`: it supplies the second coset. -/
theorem twist_mem_permitted {W : Finset α} {a b c d : α} (ha : a ∈ W) (hb : b ∈ W)
    (hab : a ≠ b) (hc : c ∉ W) (hd : d ∉ W) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup α ∧
      swap a b * swap c d ∈ sides W Wᶜ := by
  have hac : a ≠ c := fun h => hc (h ▸ ha)
  have had : a ≠ d := fun h => hd (h ▸ ha)
  have hbc : b ≠ c := fun h => hc (h ▸ hb)
  have hbd : b ≠ d := fun h => hd (h ▸ hb)
  refine ⟨?_, mem_sides_of_maps _ ?_ ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]; rfl
  · intro x hx
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    have hxd : x ≠ d := fun h => hd (h ▸ hx)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd]
    rcases eq_or_ne x a with rfl | hxa
    · rw [swap_apply_left]; exact hb
    rcases eq_or_ne x b with rfl | hxb
    · rw [swap_apply_right]; exact ha
    rw [swap_apply_of_ne_of_ne hxa hxb]; exact hx
  · intro x hx
    rw [Finset.mem_compl] at hx ⊢
    have hxa : x ≠ a := fun h => hx (h ▸ ha)
    have hxb : x ≠ b := fun h => hx (h ▸ hb)
    rw [Perm.mul_apply]
    rcases eq_or_ne x c with rfl | hxc
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]; exact hd
    rcases eq_or_ne x d with rfl | hxd
    · rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]; exact hc
    rw [swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]; exact hx

/-- A permitted `t` whose `W`-side is odd is outside `Alt(W) × Alt(C)`, and every
permitted `g` lies in `Alt(W) × Alt(C)` or in `t (Alt(W) × Alt(C))`. -/
theorem mem_evenSides_or_twist (W : Finset α) (t g : permitted W Wᶜ)
    (ht : sign (sideAction t).1 = -1) :
    (t : alternatingGroup α) ∉ evenSides W Wᶜ ∧
      ((g : alternatingGroup α) ∈ evenSides W Wᶜ ∨
        ((t⁻¹ * g : permitted W Wᶜ) : alternatingGroup α) ∈ evenSides W Wᶜ) := by
  rw [mem_evenSides_compl_iff, mem_evenSides_compl_iff, mem_evenSides_compl_iff, ht]
  refine ⟨by decide, ?_⟩
  rw [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, Perm.sign_mul, sign_inv, ht]
  rcases Int.units_eq_one_or (sign (sideAction g).1) with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h]; rfl)

/-- The `W`-side of the paired transposition `(a b)(c d)`, `a ≠ b`, is odd. -/
theorem twist_side_sign {W : Finset α} {a b c d : α} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b)
    (hc : c ∉ W) (hd : d ∉ W) (t : permitted W Wᶜ)
    (ht : ((t : alternatingGroup α) : Perm α) = swap a b * swap c d) :
    sign (sideAction t).1 = -1 := by
  have hside : (sideAction t).1 = swap ⟨a, ha⟩ ⟨b, hb⟩ := by
    refine Equiv.ext fun x => Subtype.ext ?_
    change ((t : alternatingGroup α) : Perm α) x.val = _
    have hxc : x.val ≠ c := fun h => hc (h ▸ x.property)
    have hxd : x.val ≠ d := fun h => hd (h ▸ x.property)
    rw [ht, Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd]
    rcases eq_or_ne x ⟨a, ha⟩ with rfl | hxa
    · rw [swap_apply_left, swap_apply_left]
    rcases eq_or_ne x ⟨b, hb⟩ with rfl | hxb
    · rw [swap_apply_right, swap_apply_right]
    have hxa' : x.val ≠ a := fun h => hxa (Subtype.ext h)
    have hxb' : x.val ≠ b := fun h => hxb (Subtype.ext h)
    rw [swap_apply_of_ne_of_ne hxa' hxb', swap_apply_of_ne_of_ne hxa hxb]
  rw [hside, sign_swap (fun h => hab (congrArg Subtype.val h))]

/-- When `|Γ \ W| ≤ 1` there is no second coset: every permitted permutation has an
even `W`-side, since its `C`-side is a permutation of at most one point. -/
theorem permitted_le_evenSides_of_small (W : Finset α) (hC : Wᶜ.card ≤ 1) :
    permitted W Wᶜ ≤ evenSides W Wᶜ := by
  intro g hg
  have hs := sideAction_sign disjoint_compl_right (by simp) ⟨g, hg⟩
  have h2 : sign (sideAction (⟨g, hg⟩ : permitted W Wᶜ)).2 = 1 := by
    haveI : Subsingleton (Wᶜ : Finset α) := by
      rw [← Finset.card_le_one_iff_subsingleton_coe]; exact hC
    rw [Subsingleton.elim (sideAction (⟨g, hg⟩ : permitted W Wᶜ)).2 1, sign_one]
  rw [h2, mul_one] at hs
  exact (mem_evenSides_compl_iff W ⟨g, hg⟩).mpr hs

/-- The `W`-side of an element of `Alt(W) × Alt(R)`, an even permutation of `W`. -/
def evenLeft (W R : Finset α) : evenSides W R →* alternatingGroup W :=
  (((MonoidHom.fst _ _).comp sideAction).comp (Subgroup.inclusion evenSides_le)).codRestrict
    (alternatingGroup W) (fun g => by
      obtain ⟨_, h1, -⟩ := (mem_evenSides_iff (W := W) (R := R) g.val).mp g.property
      exact h1)

theorem evenLeft_apply (g : evenSides W R) (a : W) :
    ((evenLeft W R g : alternatingGroup W) : Perm W) a =
      ⟨((g : alternatingGroup α) : Perm α) a, (left_mem_iff W R ⟨g, evenSides_le g.property⟩ a).mpr
        a.property⟩ := rfl

/-- `Alt(W) × Alt(R)` maps onto `Alt(W)`: an even `σ` is the `W`-side of
`sidePerm σ 1`. -/
theorem evenLeft_surjective (hd : Disjoint W R) : Function.Surjective (evenLeft W R) := by
  intro σ
  obtain ⟨g, hg⟩ := exists_sideAction_of_even hd (σ : Perm W) 1
    (by rw [sign_one, mul_one]; exact σ.property)
  have hmem : (g : alternatingGroup α) ∈ evenSides W R :=
    (mem_evenSides_iff _).mpr ⟨g.property, by rw [hg]; exact σ.property,
      by rw [hg]; exact sign_one⟩
  refine ⟨⟨g, hmem⟩, Subtype.ext ?_⟩
  change (sideAction g).1 = σ
  rw [hg]

/-- The kernel of `evenLeft` is `1_W × Alt(R)`: the elements fixing `W` pointwise. -/
theorem evenLeft_eq_one_iff (g : evenSides W R) :
    evenLeft W R g = 1 ↔ ∀ a ∈ W, ((g : alternatingGroup α) : Perm α) a = a := by
  constructor
  · intro h a ha
    have := congrArg (fun σ : alternatingGroup W => ((σ : Perm W) ⟨a, ha⟩ : α)) h
    exact this
  · intro h
    refine Subtype.ext (Equiv.ext fun a => Subtype.ext ?_)
    exact h a.val a.property

/-! ### Aligning source and target sides by an even permutation -/

/-- **Alignment** ("choose an even bijection of `Γ` taking the three source parts to
the three target parts ... Such a bijection exists since `|W_X| ≥ 3`: the sign of any
alignment can be corrected inside its `W_Y` part"). Two points of `W` suffice. -/
theorem exists_even_alignment {W R W' R' : Finset α} (hd : Disjoint W R)
    (hd' : Disjoint W' R') (hW : W.card = W'.card) (hR : R.card = R'.card)
    (h2 : 2 ≤ W.card) :
    ∃ g : alternatingGroup α, (g : Perm α) '' (W : Set α) = W' ∧
      (g : Perm α) '' (R : Set α) = R' := by
  classical
  obtain ⟨eW⟩ : Nonempty (W ≃ W') := by
    rw [← Fintype.card_eq]; simpa using hW
  obtain ⟨eR⟩ : Nonempty (R ≃ R') := by
    rw [← Fintype.card_eq]; simpa using hR
  let f : α → α := fun a =>
    if h : a ∈ W then (eW ⟨a, h⟩ : α) else if h' : a ∈ R then (eR ⟨a, h'⟩ : α) else a
  have fW : ∀ a (h : a ∈ W), f a = eW ⟨a, h⟩ := fun a h => by simp [f, h]
  have fR : ∀ a (h : a ∈ R), f a = eR ⟨a, h⟩ := fun a h => by
    have hW : a ∉ W := fun hw => Finset.disjoint_left.mp hd hw h
    simp [f, h, hW]
  have hinj : Set.InjOn f ((W ∪ R : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [fW a ha, fW b hb] at hab
      exact congrArg Subtype.val (eW.injective (Subtype.ext hab))
    · rw [fW a ha, fR b hb] at hab
      exact absurd ((eR ⟨b, hb⟩).property) (hab ▸ Finset.disjoint_left.mp hd' (eW ⟨a, ha⟩).property)
    · rw [fR a ha, fW b hb] at hab
      exact absurd ((eW ⟨b, hb⟩).property)
        (hab ▸ Finset.disjoint_right.mp hd' (eR ⟨a, ha⟩).property)
    · rw [fR a ha, fR b hb] at hab
      exact congrArg Subtype.val (eR.injective (Subtype.ext hab))
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := Finset.univ) (by simp)
    (Finset.subset_univ _) hinj
  let p : Perm α := g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ)
  have hp : ∀ a ∈ W ∪ R, p a = f a := fun a ha => hg a ha
  have pW : ∀ a ∈ W, p a ∈ W' := fun a ha => by
    rw [hp a (Finset.mem_union_left _ ha), fW a ha]; exact Subtype.property _
  have pR : ∀ a ∈ R, p a ∈ R' := fun a ha => by
    rw [hp a (Finset.mem_union_right _ ha), fR a ha]; exact Subtype.property _
  -- A permutation mapping `W` into `W'` with `|W| = |W'|` maps it onto `W'`.
  have onto : ∀ (q : Perm α) (S S' : Finset α), S.card = S'.card → (∀ a ∈ S, q a ∈ S') →
      q '' (S : Set α) = S' := by
    intro q S S' hc hS
    have hsub : S.map q.toEmbedding ⊆ S' := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact hS a ha
    have heq : S.map q.toEmbedding = S' :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map, hc])
    rw [← heq, Finset.coe_map]
    rfl
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < W'.card)
  have hxR : x ∉ R' := fun h => Finset.disjoint_left.mp hd' hx h
  have hyR : y ∉ R' := fun h => Finset.disjoint_left.mp hd' hy h
  have swW : ∀ b ∈ W', swap x y b ∈ W' := by
    intro b hb
    rcases eq_or_ne b x with rfl | hbx
    · rw [swap_apply_left]; exact hy
    rcases eq_or_ne b y with rfl | hby
    · rw [swap_apply_right]; exact hx
    rw [swap_apply_of_ne_of_ne hbx hby]; exact hb
  have swR : ∀ b ∈ R', swap x y b = b := fun b hb =>
    swap_apply_of_ne_of_ne (fun h => hxR (h ▸ hb)) (fun h => hyR (h ▸ hb))
  by_cases hs : sign p = 1
  · exact ⟨⟨p, hs⟩, onto p W W' hW pW, onto p R R' hR pR⟩
  · have hs' : sign (swap x y * p) = 1 := by
      rw [Perm.sign_mul, sign_swap hxy]
      rcases Int.units_eq_one_or (sign p) with h | h
      · exact absurd h hs
      · rw [h]; rfl
    refine ⟨⟨swap x y * p, hs'⟩, onto _ W W' hW fun a ha => swW _ (pW a ha),
      onto _ R R' hR fun a ha => ?_⟩
    change swap x y (p a) ∈ R'
    rw [swR _ (pR a ha)]
    exact pR a ha

/-- **The alignment coset**: "This fixes one alignment coset; the subgroup in Lemma A.27
then supplies all remaining possibilities." If `g₀` aligns `(W, R)` with `(W', R')`,
the aligning even permutations are exactly `g₀ P`. -/
theorem alignment_coset {W R W' R' : Finset α} (g₀ : alternatingGroup α)
    (hW : (g₀ : Perm α) '' (W : Set α) = W') (hR : (g₀ : Perm α) '' (R : Set α) = R')
    (g : alternatingGroup α) :
    ((g : Perm α) '' (W : Set α) = W' ∧ (g : Perm α) '' (R : Set α) = R') ↔
      g₀⁻¹ * g ∈ permitted W R := by
  have key : ∀ S : Finset α, ∀ S' : Set α, (g₀ : Perm α) '' (S : Set α) = S' →
      ((g : Perm α) '' (S : Set α) = S' ↔
        ((g₀⁻¹ * g : alternatingGroup α) : Perm α) ∈
          MulAction.stabilizer (Perm α) (S : Set α)) := by
    intro S S' h0
    have e : ((g₀⁻¹ * g : alternatingGroup α) : Perm α) • (S : Set α) =
        ((((g₀ : Perm α))⁻¹ : Perm α) : α → α) '' ((g : Perm α) '' (S : Set α)) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [MulAction.mem_stabilizer_iff, e]
    constructor
    · intro h
      rw [h, ← h0, Set.image_image]
      simp
    · intro h
      calc (g : Perm α) '' (S : Set α)
          = (g₀ : Perm α) '' (((((g₀ : Perm α))⁻¹ : Perm α) : α → α) '' ((g : Perm α) '' (S : Set α))) := by
            rw [Set.image_image]; simp
        _ = S' := by rw [h, h0]
  rw [key W W' hW, key R R' hR]
  rfl

end GI.Rectangle
