module

public import Workspace.Impl.AggItemCiCfgM

@[expose] public section

/-!
# The configuration query: the outer color classes

The proof of Lemma A.12 combines `Aut(C)` "with the Young groups on the outer color classes"
and "align[s] those classes". The outer points of a pair configuration `Z` are the points
outside the fiber. The outer color class of a color `c` is the set of outer points `a` with
`Z.col a a = c`.

To align the classes, the program lists the outer points by color (`itciFo Z`): ordered by
the key `(Z.col a a, a)`, so the outer classes come one after the other, by increasing color.
`Lang/Lib` has no sort, so the list is built from ranks. The rank `itciRk Z a` of an outer point
`a` is the number of outer points with a smaller key, and entry `i` of `itciFo Z` is the outer
point of rank `i` (`itciAt Z i`, found by `idxOf` in the list of ranks).

* `itci_mem_fo`, `itciFo_nodup`, `itciFo_length`: `itciFo Z` lists each outer point once.
* `ItciAl X Y`: the colors along `itciFo X` and along `itciFo Y` agree. Then entry `k` of both
  lists has the same color (`itci_al_get`), so the map from entry `k` to entry `k` aligns the
  classes.
* `itci_al_of_maps`: if some map keeps the fibers and the outer color classes, then
  `ItciAl X Y`. Both color lists are sorted, and the map shows that they have the same entries.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset

variable {q : ℕ}

/-- The diagonal colors of the outer points, in increasing order of the points. -/
def itciOc (Z : PairCfg q) : List ℕ := (itciFl Z.fiberᶜ).map fun a => Z.col a a

/-- The order of the keys `(Z.col a a, a)`: `b` comes before `a`. -/
def itciLt (Z : PairCfg q) (b a : Fin q) : Bool :=
  decide (Z.col b b < Z.col a a ∨ (Z.col b b = Z.col a a ∧ b < a))

/-- **The rank of a point**: the number of outer points before it. -/
def itciRk (Z : PairCfg q) (a : Fin q) : ℕ := ((itciFl Z.fiberᶜ).filter fun b => itciLt Z b a).length

/-- The outer point of rank `i`, read from the list of ranks. -/
def itciAt (Z : PairCfg q) (i : ℕ) : Option (Fin q) :=
  (itciFl Z.fiberᶜ)[((itciFl Z.fiberᶜ).map (itciRk Z)).idxOf i]?

/-- **The outer points by color**: entry `i` is the outer point of rank `i`. -/
def itciFo (Z : PairCfg q) : List (Fin q) :=
  (List.range (itciFl Z.fiberᶜ).length).filterMap (itciAt Z)

/-! ### The order of the keys -/

theorem itciLt_irrefl (Z : PairCfg q) (a : Fin q) : itciLt Z a a = false := by
  simp [itciLt]

theorem itciLt_trans {Z : PairCfg q} {a b c : Fin q} (h1 : itciLt Z a b) (h2 : itciLt Z b c) :
    itciLt Z a c := by
  simp only [itciLt, decide_eq_true_eq] at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem itciLt_total {Z : PairCfg q} {a b : Fin q} (h : a ≠ b) :
    itciLt Z a b ∨ itciLt Z b a := by
  simp only [itciLt, decide_eq_true_eq]
  rcases lt_trichotomy (Z.col a a) (Z.col b b) with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_or_gt_of_ne h with h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

/-- A sublist with an extra point is longer. -/
private theorem itci_len_lt {l₁ l₂ : List (Fin q)} (hs : List.Sublist l₁ l₂) {x : Fin q} (h1 : x ∉ l₁)
    (h2 : x ∈ l₂) : l₁.length < l₂.length := by
  rcases lt_or_eq_of_le hs.length_le with h | h
  · exact h
  · exact absurd ((hs.eq_of_length h) ▸ h2) h1

/-- **The rank is monotone in the key.** -/
theorem itciRk_lt {Z : PairCfg q} {a b : Fin q} (hb : b ∉ Z.fiber) (h : itciLt Z b a) :
    itciRk Z b < itciRk Z a := by
  refine itci_len_lt (List.monotone_filter_right _ fun c hc => itciLt_trans hc h)
    (x := b) ?_ ?_
  · simp [itciLt_irrefl]
  · simp [itci_mem_fl, hb, h]

theorem itciRk_lt_length (Z : PairCfg q) {a : Fin q} (ha : a ∉ Z.fiber) :
    itciRk Z a < (itciFl Z.fiberᶜ).length :=
  itci_len_lt (List.filter_sublist) (x := a) (by simp [itciLt_irrefl])
    (itci_mem_fl.2 (Finset.mem_compl.2 ha))

theorem itciRk_inj {Z : PairCfg q} {a b : Fin q} (ha : a ∉ Z.fiber) (hb : b ∉ Z.fiber)
    (h : itciRk Z a = itciRk Z b) : a = b := by
  by_contra hne
  rcases itciLt_total (Z := Z) hne with h1 | h1
  · exact absurd h (itciRk_lt ha h1).ne
  · exact absurd h (itciRk_lt hb h1).ne'

/-- Every rank below the number of outer points is taken. -/
theorem itciRk_surj (Z : PairCfg q) {i : ℕ} (hi : i < (itciFl Z.fiberᶜ).length) :
    ∃ a, a ∉ Z.fiber ∧ itciRk Z a = i := by
  classical
  have hsub : Z.fiberᶜ.image (itciRk Z) ⊆ Finset.range (itciFl Z.fiberᶜ).length := fun r hr => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    exact Finset.mem_range.2 (itciRk_lt_length Z (Finset.mem_compl.1 ha))
  have hcard : (Finset.range (itciFl Z.fiberᶜ).length).card ≤ (Z.fiberᶜ.image (itciRk Z)).card := by
    rw [Finset.card_range, Finset.card_image_of_injOn (fun a ha b hb h =>
      itciRk_inj (Finset.mem_compl.1 ha) (Finset.mem_compl.1 hb) h), itciFl_length]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  obtain ⟨a, ha, h⟩ := Finset.mem_image.1 (this ▸ Finset.mem_range.2 hi)
  exact ⟨a, Finset.mem_compl.1 ha, h⟩

theorem itciAt_rk {Z : PairCfg q} {i : ℕ} {a : Fin q} (h : itciAt Z i = some a) :
    a ∉ Z.fiber ∧ itciRk Z a = i := by
  unfold itciAt at h
  set D := itciFl Z.fiberᶜ
  have hlt : ((D.map (itciRk Z)).idxOf i) < D.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h
  subst h
  refine ⟨Finset.mem_compl.1 (itci_mem_fl.1 (List.getElem_mem hlt)), ?_⟩
  have hlt' : (D.map (itciRk Z)).idxOf i < (D.map (itciRk Z)).length := by simpa using hlt
  have := List.getElem_idxOf hlt'
  rw [List.getElem_map] at this
  exact this

theorem itciAt_some (Z : PairCfg q) {i : ℕ} (hi : i < (itciFl Z.fiberᶜ).length) :
    ∃ a, itciAt Z i = some a := by
  obtain ⟨b, hb, rfl⟩ := itciRk_surj Z hi
  have hm : itciRk Z b ∈ (itciFl Z.fiberᶜ).map (itciRk Z) :=
    List.mem_map.2 ⟨b, itci_mem_fl.2 (Finset.mem_compl.2 hb), rfl⟩
  have hlt := List.idxOf_lt_length_iff.2 hm
  rw [List.length_map] at hlt
  exact ⟨_, List.getElem?_eq_getElem hlt⟩

theorem itci_mem_fo {Z : PairCfg q} {a : Fin q} : a ∈ itciFo Z ↔ a ∉ Z.fiber := by
  simp only [itciFo, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, -, h⟩; exact (itciAt_rk h).1
  · intro ha
    obtain ⟨b, hb⟩ := itciAt_some Z (itciRk_lt_length Z ha)
    refine ⟨_, itciRk_lt_length Z ha, ?_⟩
    obtain ⟨hb', he⟩ := itciAt_rk hb
    rw [hb, itciRk_inj hb' ha he]

theorem itciFo_nodup (Z : PairCfg q) : (itciFo Z).Nodup :=
  List.Nodup.filterMap (fun _ _ _ h h' => (itciAt_rk h).2.symm.trans (itciAt_rk h').2)
    List.nodup_range

theorem itciFo_perm (Z : PairCfg q) : (itciFo Z).Perm (itciFl Z.fiberᶜ) :=
  (List.perm_ext_iff_of_nodup (itciFo_nodup Z) (itciFl_nodup _)).2 fun a => by
    rw [itci_mem_fo, itci_mem_fl, Finset.mem_compl]

theorem itciFo_length (Z : PairCfg q) : (itciFo Z).length = Z.fiberᶜ.card := by
  rw [(itciFo_perm Z).length_eq, itciFl_length]

/-- **The list is sorted by the key**, so its colors increase. -/
theorem itciFo_sorted (Z : PairCfg q) : (itciFo Z).Pairwise fun a b => itciLt Z a b := by
  refine List.Pairwise.filterMap _ (fun i i' hii' b hb b' hb' => ?_) List.pairwise_lt_range
  obtain ⟨hbf, hbr⟩ := itciAt_rk hb
  obtain ⟨hbf', hbr'⟩ := itciAt_rk hb'
  have hne : b ≠ b' := fun e => by subst e; omega
  rcases itciLt_total (Z := Z) hne with h | h
  · exact h
  · have := itciRk_lt hbf' h; omega

theorem itciFo_cols_sorted (Z : PairCfg q) :
    ((itciFo Z).map fun a => Z.col a a).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  refine (itciFo_sorted Z).imp fun {a b} h => ?_
  simp only [itciLt, decide_eq_true_eq] at h
  omega

/-! ### Aligned classes -/

/-- **The outer classes of `X` and `Y` can be aligned in order**: the colors along `itciFo X`
and `itciFo Y` agree. -/
def ItciAl (X Y : PairCfg q) : Prop :=
  (itciFo X).map (fun a => X.col a a) = (itciFo Y).map (fun a => Y.col a a)

theorem itci_al_self (X : PairCfg q) : ItciAl X X := rfl

/-- Entry `k` of `itciFo X` and entry `k` of `itciFo Y` have the same color. -/
theorem itci_al_get {X Y : PairCfg q} (hal : ItciAl X Y) (k : ℕ) (hX : k < (itciFo X).length)
    (hY : k < (itciFo Y).length) :
    Y.col (itciFo Y)[k] (itciFo Y)[k] = X.col (itciFo X)[k] (itciFo X)[k] := by
  have h1 := List.getElem_of_eq hal (i := k) (by simpa using hX)
  simp only [List.getElem_map] at h1
  exact h1.symm

open List in
/-- **A map that keeps the fibers and the outer color classes exists only if the classes can be
aligned.** -/
theorem itci_al_of_maps {X Y : PairCfg q} {σ : Perm (Fin q)} (hσ : PairCfg.Maps X Y σ) :
    ItciAl X Y := by
  refine List.Perm.eq_of_pairwise' (itciFo_cols_sorted X) (itciFo_cols_sorted Y) ?_
  -- `σ` maps the outer points of `X` onto those of `Y` and keeps their colors
  have hD : ((itciFl X.fiberᶜ).map σ).Perm (itciFl Y.fiberᶜ) := by
    refine (List.perm_ext_iff_of_nodup ((itciFl_nodup _).map σ.injective) (itciFl_nodup _)).2
      fun b => ?_
    simp only [List.mem_map, itci_mem_fl, Finset.mem_compl]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact fun h => ha ((hσ.1 a).1 h)
    · intro hb
      exact ⟨σ⁻¹ b, fun h => hb (by have := (hσ.1 (σ⁻¹ b)).2 h; rwa [Perm.apply_inv_self] at this),
        Perm.apply_inv_self σ b⟩
  have hc : ((itciFl X.fiberᶜ).map fun a => X.col a a) =
      ((itciFl X.fiberᶜ).map σ).map fun b => Y.col b b := by
    rw [List.map_map]
    refine List.map_congr_left fun a ha => ?_
    exact (hσ.2.2 a (Finset.mem_compl.1 (itci_mem_fl.1 ha))).symm
  calc ((itciFo X).map fun a => X.col a a)
      _ ~ ((itciFl X.fiberᶜ).map fun a => X.col a a) := (itciFo_perm X).map _
      _ = (((itciFl X.fiberᶜ).map σ).map fun b => Y.col b b) := hc
      _ ~ ((itciFl Y.fiberᶜ).map fun b => Y.col b b) := hD.map _
      _ ~ ((itciFo Y).map fun b => Y.col b b) := ((itciFo_perm Y).map _).symm

end GI.Impl
