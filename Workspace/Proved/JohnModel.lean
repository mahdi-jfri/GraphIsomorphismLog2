module

public import Workspace.Proved.JohnOrbital
public import Workspace.Lang.Lib.NatList

@[expose] public section

/-!
# Finding the two orbitals `Υ` and `Δ` of [H, §2.8]

The program has a list `labL` of `n * n` labels: entry `n * x + y` is the label of the orbit of
the pair `(x, y)`. By `john_lab_iff`, two pairs have the same label exactly when their `k`-sets
meet in the same number of elements. From the labels the program finds two of them:

* `Δ`, the label of the disjoint pairs. It is the label `y ↦ lab(0, y)` that occurs most often
  in row `0`, since by `john_val_lt` the disjoint `k`-sets are the most numerous.
* `Υ`, the label of the pairs that meet in `k - 1` elements. Its label occurs `k (m - k)` times
  in row `0`, and no other label does.

This file defines these steps on lists (`johnRow`, `johnCnt`, `johnDelta`, `johnUps`) and proves
`john_delta_iff` and `john_ups_iff`, the only results used later.
-/

namespace GI.Proved

open Equiv Finset GI.Cited

variable {n m k : ℕ}

/-- The hypotheses: the promise of the task on `m, k`, and the labels of the pairs. -/
structure JohnHyp (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (lab : Fin (n * n) → ℕ) :
    Prop where
  five_le : 5 ≤ m
  one_le : 1 ≤ k
  bound : (k + 1) ^ 2 < m + 2
  lab_iff : ∀ x y x' y', lab (johnPair x y) = lab (johnPair x' y') ↔
    johnInter ι x y = johnInter ι x' y'

section
variable {ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}} {lab : Fin (n * n) → ℕ}

theorem JohnHyp.sq (h : JohnHyp ι lab) : k * k + 2 * k ≤ m := by
  have := h.bound
  nlinarith

theorem JohnHyp.two_mul (h : JohnHyp ι lab) : 2 * k + 2 ≤ m := by
  have := h.sq; have := h.one_le; have := h.five_le
  rcases Nat.lt_or_ge k 2 with hk | hk
  · omega
  · nlinarith

theorem JohnHyp.three_mul (h : JohnHyp ι lab) : 3 * k ≤ m := by
  have := h.sq; have := h.one_le
  nlinarith

/-- A `k`-set exists, so there is a point. -/
theorem JohnHyp.pos (h : JohnHyp ι lab) : 0 < n := by
  have := h.two_mul
  obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin m))) (n := k)
    (by rw [card_univ, Fintype.card_fin]; omega)
  exact Fin.pos (ι.symm ⟨A, hA⟩)

/-- The base point `0`. -/
def JohnHyp.x0 (h : JohnHyp ι lab) : Fin n := ⟨0, h.pos⟩

end

/-! ### The lists -/

/-- The labels as a list. -/
def johnLabL (lab : Fin (n * n) → ℕ) : List ℕ := (List.finRange (n * n)).map lab

/-- Row `0` of the labels. -/
def johnRow (n : ℕ) (labL : List ℕ) : List ℕ := (List.range n).map fun y => labL.getD y 0

/-- How often each entry of the row occurs in it. -/
def johnCnt (row : List ℕ) : List ℕ := row.map fun j => row.count j

/-- The label that occurs most often in the row. -/
def johnDelta (row : List ℕ) : ℕ :=
  row.getD ((johnCnt row).findIdx fun c => decide (c = (johnCnt row).foldl max 0)) 0

/-- The label that occurs `k (m - k)` times in the row. -/
def johnUps (m k : ℕ) (row : List ℕ) : ℕ :=
  row.getD ((johnCnt row).findIdx fun c => decide (c = k * (m - k))) 0

theorem john_labL_getD (lab : Fin (n * n) → ℕ) (x y : Fin n) :
    (johnLabL lab).getD (n * x + y) 0 = lab (johnPair x y) := by
  have hlt : n * x + y < n * n := by rw [← john_pair_val]; exact (johnPair x y).isLt
  have hlt' : n * x + y < (List.finRange (n * n)).length := by simpa using hlt
  have he : (List.finRange (n * n))[n * x + y]'hlt' = johnPair x y := by
    ext; simp [john_pair_val]
  rw [johnLabL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt',
    he]
  rfl

theorem john_count_finRange (p : Fin n → Bool) :
    (List.finRange n).countP p = #(univ.filter fun x => p x = true) := by
  rw [card_def, filter_val, Fin.univ_def]
  simp [List.countP_eq_length_filter]

section
variable {ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}} {lab : Fin (n * n) → ℕ}

theorem john_row_eq (h : JohnHyp ι lab) :
    johnRow n (johnLabL lab) = (List.finRange n).map fun z => lab (johnPair h.x0 z) := by
  rw [johnRow, ← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun z _ => ?_
  have := john_labL_getD lab h.x0 z
  simp only [JohnHyp.x0, mul_zero, zero_add] at this
  exact this

theorem john_inter_le (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (x y : Fin n) :
    johnInter ι x y ≤ k :=
  (card_le_card inter_subset_left).trans (ι x).2.le

/-- The number of points whose `k`-set meets a given `k`-set `A` in `i` elements. -/
theorem john_card_points (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (x : Fin n) (i : ℕ) :
    #(univ.filter fun z => johnInter ι x z = i) =
      #((powersetCard k (univ : Finset (Fin m))).filter fun Z => #((ι x).1 ∩ Z) = i) := by
  refine card_nbij' (fun z => (ι z).1) (fun Z => if hZ : #Z = k then ι.symm ⟨Z, hZ⟩ else x)
    ?_ ?_ ?_ ?_
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq]
    exact ⟨(ι z).2, hz⟩
  · intro Z hZ
    simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hZ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, hZ.1, dif_pos]
    simp [johnInter, hZ.2]
  · intro z _
    simp [(ι z).2]
  · intro Z hZ
    simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hZ
    simp [hZ.1]

/-- **The count of a label in row `0`.** -/
theorem john_row_count (h : JohnHyp ι lab) (y : Fin n) :
    (johnRow n (johnLabL lab)).count (lab (johnPair h.x0 y)) =
      johnVal m k (k - johnInter ι h.x0 y) := by
  rw [john_row_eq h, List.count_eq_countP, List.countP_map, john_count_finRange]
  have hle := john_inter_le ι h.x0 y
  rw [← john_card_val (ι h.x0).1 (ι h.x0).2 _ (by omega), show k - (k - johnInter ι h.x0 y) =
    johnInter ι h.x0 y by omega, ← john_card_points]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, Function.comp_apply, beq_iff_eq]
  exact h.lab_iff _ _ _ _

theorem john_cnt_eq (h : JohnHyp ι lab) :
    johnCnt (johnRow n (johnLabL lab)) =
      (List.finRange n).map fun y => johnVal m k (k - johnInter ι h.x0 y) := by
  unfold johnCnt
  rw [john_row_eq h, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  have := john_row_count h y
  rw [john_row_eq h] at this
  exact this

theorem john_val_inj (hb : (k + 1) ^ 2 < m + 2) {j j' : ℕ} (hj : j ≤ k) (hj' : j' ≤ k)
    (he : johnVal m k j = johnVal m k j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd he (john_val_lt hb hlt hj').ne
  · exact heq
  · exact absurd he (john_val_lt hb hgt hj).ne'

/-- A point whose `k`-set meets that of `x` in a given number `i ≤ k` of elements, when
`2 k ≤ m`. -/
theorem john_exists_inter (ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}) (hkm : 2 * k ≤ m)
    (x : Fin n) (i : ℕ) (hi : i ≤ k) : ∃ y, johnInter ι x y = i := by
  set A := (ι x).1
  have hA : #A = k := (ι x).2
  obtain ⟨S, hSA, hS⟩ := exists_subset_card_eq (s := A) (n := i) (by omega)
  obtain ⟨T, hTA, hT⟩ := exists_subset_card_eq (s := Aᶜ) (n := k - i)
    (by rw [card_compl, Fintype.card_fin]; omega)
  have hdis : Disjoint S T :=
    disjoint_of_subset_left hSA (disjoint_of_subset_right hTA disjoint_compl_right)
  have hcard : #(S ∪ T) = k := by rw [card_union_of_disjoint hdis, hS, hT]; omega
  refine ⟨ι.symm ⟨S ∪ T, hcard⟩, ?_⟩
  unfold johnInter
  rw [Equiv.apply_symm_apply]
  have : A ∩ (S ∪ T) = S := by
    ext a
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨haA, h | h⟩
      · exact h
      · exact absurd haA (mem_compl.mp (hTA h))
    · intro h; exact ⟨hSA h, Or.inl h⟩
  change #(A ∩ (S ∪ T)) = i
  rw [this, hS]

/-- The index that `findIdx` returns for an entry that occurs. -/
theorem john_findIdx {l : List ℕ} {c : ℕ} (hc : c ∈ l) :
    ∃ hlt : l.findIdx (fun x => decide (x = c)) < l.length,
      l[l.findIdx (fun x => decide (x = c))] = c := by
  have hlt : l.findIdx (fun x => decide (x = c)) < l.length :=
    List.findIdx_lt_length_of_exists ⟨c, hc, by simp⟩
  exact ⟨hlt, by simpa using List.findIdx_getElem (w := hlt)⟩

/-- The entry of the row at the index of an entry of the counts. -/
theorem john_row_getD (h : JohnHyp ι lab) {t : ℕ} (ht : t < n) :
    (johnRow n (johnLabL lab)).getD t 0 = lab (johnPair h.x0 ⟨t, ht⟩) := by
  rw [john_row_eq h]
  simp [List.getD_eq_getElem?_getD, ht]

theorem john_cnt_getElem (h : JohnHyp ι lab) {t : ℕ} (ht : t < (johnCnt (johnRow n (johnLabL lab))).length) :
    ∃ ht' : t < n, (johnCnt (johnRow n (johnLabL lab)))[t] =
      johnVal m k (k - johnInter ι h.x0 ⟨t, ht'⟩) := by
  have ht' : t < n := by
    have := ht; rw [john_cnt_eq h] at this; simpa using this
  refine ⟨ht', ?_⟩
  simp only [john_cnt_eq h, List.getElem_map, List.getElem_finRange]
  rfl

/-- The largest count in row `0` is the valency of the disjoint pairs. -/
theorem john_cnt_max (h : JohnHyp ι lab) :
    (johnCnt (johnRow n (johnLabL lab))).foldl max 0 = johnVal m k k := by
  have hkm : 2 * k ≤ m := by have := h.two_mul; omega
  set cnt := johnCnt (johnRow n (johnLabL lab)) with hcnt
  apply le_antisymm
  · apply GI.Lang.foldl_max_le (Nat.zero_le _)
    intro c hc
    rw [hcnt, john_cnt_eq h] at hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
    rcases Nat.eq_or_lt_of_le (Nat.sub_le k (johnInter ι h.x0 y)) with he | hlt
    · rw [he]
    · exact (john_val_lt h.bound hlt le_rfl).le
  · obtain ⟨y, hy⟩ := john_exists_inter ι hkm h.x0 0 (Nat.zero_le _)
    have hmem : johnVal m k k ∈ cnt := by
      rw [hcnt, john_cnt_eq h]
      exact List.mem_map.mpr ⟨y, List.mem_finRange _, by rw [hy, Nat.sub_zero]⟩
    exact (GI.Lang.le_foldl_max cnt 0).2 _ hmem

/-- The largest count is one of the counts. -/
theorem john_max_mem (h : JohnHyp ι lab) :
    (johnCnt (johnRow n (johnLabL lab))).foldl max 0 ∈ johnCnt (johnRow n (johnLabL lab)) := by
  have hkm : 2 * k ≤ m := by have := h.two_mul; omega
  rcases GI.Lang.foldl_max_mem (johnCnt (johnRow n (johnLabL lab))) 0 with h0 | h0
  · exfalso
    rw [john_cnt_max h] at h0
    exact (john_val_pos (le_refl k) hkm).ne' h0
  · exact h0

/-- The valency `k (m - k)` is one of the counts. -/
theorem john_ups_mem (h : JohnHyp ι lab) : k * (m - k) ∈ johnCnt (johnRow n (johnLabL lab)) := by
  have hkm : 2 * k ≤ m := by have := h.two_mul; omega
  have hk := h.one_le
  obtain ⟨y, hy⟩ := john_exists_inter ι hkm h.x0 (k - 1) (Nat.sub_le _ _)
  rw [john_cnt_eq h]
  exact List.mem_map.mpr ⟨y, List.mem_finRange _, by
    rw [hy, show k - (k - 1) = 1 by omega, john_val_one]⟩

/-- **The label `Δ`.** -/
theorem john_delta_iff (h : JohnHyp ι lab) (x y : Fin n) :
    lab (johnPair x y) = johnDelta (johnRow n (johnLabL lab)) ↔ Disjoint (ι x).1 (ι y).1 := by
  set cnt := johnCnt (johnRow n (johnLabL lab)) with hcnt
  have hmax : cnt.foldl max 0 = johnVal m k k := john_cnt_max h
  have hmem : cnt.foldl max 0 ∈ cnt := john_max_mem h
  obtain ⟨hlt, hget⟩ := john_findIdx hmem
  obtain ⟨ht, hval⟩ := john_cnt_getElem h hlt
  have hd : johnDelta (johnRow n (johnLabL lab)) =
      lab (johnPair h.x0 ⟨_, ht⟩) := by
    unfold johnDelta
    rw [← hcnt]
    exact john_row_getD h ht
  rw [hd, h.lab_iff]
  have h0 : johnInter ι h.x0 ⟨_, ht⟩ = 0 := by
    have e : johnVal m k k = johnVal m k (k - johnInter ι h.x0 ⟨_, ht⟩) := by
      rw [← hmax]; exact hget.symm.trans hval
    have := john_val_inj h.bound (le_refl k) (Nat.sub_le _ _) e
    have := john_inter_le ι h.x0 ⟨_, ht⟩
    omega
  rw [h0, johnInter, card_eq_zero, disjoint_iff_inter_eq_empty]

/-- **The label `Υ`.** -/
theorem john_ups_iff (h : JohnHyp ι lab) (x y : Fin n) :
    lab (johnPair x y) = johnUps m k (johnRow n (johnLabL lab)) ↔ johnInter ι x y + 1 = k := by
  have hkm : 2 * k ≤ m := by have := h.two_mul; omega
  have hk := h.one_le
  set cnt := johnCnt (johnRow n (johnLabL lab)) with hcnt
  have hmem : k * (m - k) ∈ cnt := john_ups_mem h
  obtain ⟨hlt, hget⟩ := john_findIdx hmem
  obtain ⟨ht, hval⟩ := john_cnt_getElem h hlt
  have hd : johnUps m k (johnRow n (johnLabL lab)) = lab (johnPair h.x0 ⟨_, ht⟩) := by
    unfold johnUps
    rw [← hcnt]
    exact john_row_getD h ht
  rw [hd, h.lab_iff]
  have h1 : johnInter ι h.x0 ⟨_, ht⟩ + 1 = k := by
    have e : johnVal m k 1 = johnVal m k (k - johnInter ι h.x0 ⟨_, ht⟩) := by
      rw [john_val_one]; exact hget.symm.trans hval
    have := john_val_inj h.bound (by omega) (Nat.sub_le _ _) e
    have := john_inter_le ι h.x0 ⟨_, ht⟩
    omega
  omega

end

end GI.Proved
