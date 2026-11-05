module

public import Workspace.Impl.AggRectRepH

@[expose] public section

/-!
# The row numbers as the program computes them

The program stores the row partition as labels `rl` and the domain as an indicator list `dl`. It
computes, for each position `i`,

* the key `rcRKeyN dl rl k i`: the first position of the domain with the label of `i`;
* the list `rcRKeysN` of positions of the domain that are their own key, in increasing order;
* the row number `rcRRowN'`: the index of the key of `i` in that list;
* the row action of a permutation `h` of positions (`rcRRhoL`): row `r` goes to the row of
  `h(key r)`.

These are `rcRKey`, the keys `rcRKeys`, `rcRRow` and `ρ` of `AggRectRepRow.lean`
(`rcR_keyN_eq`, `rcR_rowN_eq`, `rcR_rhoL_eq`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm

variable {Ω : Type} {k : ℕ}

/-- The key of position `i`, as the program computes it. -/
def rcRKeyN (dl rl : List ℕ) (k i : ℕ) : ℕ :=
  (List.range k).findIdx fun j => dl.getD j 0 == 1 && rl.getD j 0 == rl.getD i 0

/-- The positions of the domain that are their own key, in increasing order. -/
def rcRKeysN (dl rl : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).filter fun j => dl.getD j 0 == 1 && rcRKeyN dl rl k j == j

/-- The row number of position `i`, as the program computes it. -/
def rcRRowN' (dl rl : List ℕ) (k i : ℕ) : ℕ :=
  (rcRKeysN dl rl k).findIdx fun t => t == rcRKeyN dl rl k i

/-- The row action of a permutation of positions, as the program computes it (`m` rows). -/
def rcRRhoL (dl rl : List ℕ) (k m : ℕ) (h : ℕ → ℕ) : List ℕ :=
  (List.range m).map fun r => rcRRowN' dl rl k (h ((rcRKeysN dl rl k).getD r 0))

/-! ### A sorted list -/

/-- In a strictly increasing list containing `t`, the index of `t` is the number of entries
below `t`. -/
theorem rcR_findIdx_sorted : ∀ {l : List ℕ}, l.Pairwise (· < ·) → ∀ {t : ℕ}, t ∈ l →
    l.findIdx (fun s => s == t) = (l.filter fun s => decide (s < t)).length
  | [], _, _, ht => by simp at ht
  | a :: l, hl, t, ht => by
    rw [List.pairwise_cons] at hl
    rw [List.findIdx_cons, List.filter_cons]
    rcases List.mem_cons.1 ht with rfl | ht'
    · have : l.filter (fun s => decide (s < t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro s hs
        have := hl.1 s hs
        simp only [decide_eq_true_eq]; omega
      simp only [beq_self_eq_true, cond_true, lt_irrefl, decide_false]
      rw [this]; rfl
    · have hat : a < t := hl.1 t ht'
      have hne : (a == t) = false := by simp; omega
      simp [hne, hat, rcR_findIdx_sorted hl.2 ht']

/-! ### Keys and row numbers -/

section Rows

variable (e : Ω ≃ Fin k) (D : Set Ω) (rows : Setoid Ω) (dI rlab : Fin k → ℕ)
  (hdI : ∀ i, dI i = open Classical in if e.symm i ∈ D then 1 else 0)
  (hrl : ∀ i j, rlab i = rlab j ↔ rows.r (e.symm i) (e.symm j))

/-- The list of a function on positions. -/
abbrev rcRL (F : Fin k → ℕ) : List ℕ := (List.finRange k).map F

theorem rcR_L_getD (F : Fin k → ℕ) (i : Fin k) : (rcRL F).getD i 0 = F i := by
  simp [rcRL, List.getD_eq_getElem?_getD]

include hdI hrl in
/-- The test of the key search at position `j < k`. -/
theorem rcR_key_test (v : Ω) {j : ℕ} (hj : j < k) :
    ((rcRL dI).getD j 0 == 1 && (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0) = true ↔
      e.symm ⟨j, hj⟩ ∈ D ∧ rows.r (e.symm ⟨j, hj⟩) v := by
  have h1 := rcR_L_getD dI ⟨j, hj⟩
  have h2 := rcR_L_getD rlab ⟨j, hj⟩
  have h3 := rcR_L_getD rlab (e v)
  simp only at h1 h2
  classical
  rw [h1, h2, h3, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, hdI, hrl]
  simp only [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, hb⟩
    by_contra hn
    simp only [hn, if_false] at ha
    omega
  · rintro ⟨ha, hb⟩
    refine ⟨?_, hb⟩
    simp [ha]

include hdI hrl in
/-- **The program's key is `rcRKey`.** -/
theorem rcR_keyN_eq {v : Ω} (hv : v ∈ D) :
    rcRKeyN (rcRL dI) (rcRL rlab) k (e v) = (rcRKey e D rows v : ℕ) := by
  classical
  set t := rcRKey e D rows v
  have ht := rcR_key_rel (e := e) (rows := rows) hv
  have hp : ∀ {j : ℕ} (hj : j < k), ((rcRL dI).getD j 0 == 1 &&
      (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0) = true ↔
      ⟨j, hj⟩ ∈ rcRKeySet e D rows v := by
    intro j hj
    rw [rcR_key_test e D rows dI rlab hdI hrl v hj, rcR_mem_keySet]
  unfold rcRKeyN
  have hlt : (List.range k).findIdx (fun j => (rcRL dI).getD j 0 == 1 &&
      (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0) < (List.range k).length :=
    List.findIdx_lt_length_of_exists ⟨t, List.mem_range.2 t.2, (hp t.2).2 (rcR_key_mem hv)⟩
  set j0 := (List.range k).findIdx (fun j => (rcRL dI).getD j 0 == 1 &&
      (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0)
  rw [List.length_range] at hlt
  have hj0 := List.findIdx_getElem (w := by rw [List.length_range]; exact hlt)
    (p := fun j => (rcRL dI).getD j 0 == 1 && (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0)
  rw [List.getElem_range] at hj0
  have hmem := (hp hlt).1 hj0
  have hle : t ≤ ⟨j0, hlt⟩ := by
    unfold t rcRKey
    rw [dif_pos (rcR_keySet_ne hv)]
    exact Finset.min'_le _ _ hmem
  refine le_antisymm ?_ hle
  by_contra hgt
  push Not at hgt
  have := List.not_of_lt_findIdx (p := fun j => (rcRL dI).getD j 0 == 1 &&
    (rcRL rlab).getD j 0 == (rcRL rlab).getD (e v) 0) (xs := List.range k) (i := t) hgt
  rw [List.getElem_range] at this
  have h2 := (hp t.2).2 (rcR_key_mem hv)
  rw [this] at h2
  exact Bool.false_ne_true h2

omit hdI hrl in
theorem rcR_keysN_pw : (rcRKeysN (rcRL dI) (rcRL rlab) k).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

include hdI hrl in
/-- **The program's keys are the keys.** -/
theorem rcR_keysN_mem {j : ℕ} :
    j ∈ rcRKeysN (rcRL dI) (rcRL rlab) k ↔ ∃ t ∈ rcRKeys e D rows, (t : ℕ) = j := by
  classical
  unfold rcRKeysN
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hj, ht⟩
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at ht
    have hd : (rcRL dI).getD j 0 = dI ⟨j, hj⟩ := rcR_L_getD dI ⟨j, hj⟩
    have hv : e.symm ⟨j, hj⟩ ∈ D := by
      by_contra hn
      rw [hd, hdI] at ht
      simp [hn] at ht
    have hk := rcR_keyN_eq e D rows dI rlab hdI hrl hv
    simp only [Equiv.apply_symm_apply] at hk
    refine ⟨_, rcR_key_mem_keys hv, ?_⟩
    rw [← hk]; exact ht.2
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨w, hw, rfl⟩ := rcR_mem_keys.1 ht
    have hv := (rcR_key_rel (e := e) (rows := rows) hw).1
    refine ⟨(rcRKey e D rows w).2, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    have hd : (rcRL dI).getD (rcRKey e D rows w) 0 = dI (rcRKey e D rows w) :=
      rcR_L_getD dI _
    refine ⟨by rw [hd, hdI, if_pos hv], ?_⟩
    have hk := rcR_keyN_eq e D rows dI rlab hdI hrl hv
    simp only [Equiv.apply_symm_apply] at hk
    rw [hk, rcR_key_key hw]

include hdI hrl in
theorem rcR_keysN_toFinset :
    (rcRKeysN (rcRL dI) (rcRL rlab) k).toFinset = (rcRKeys e D rows).map Fin.valEmbedding := by
  ext j
  rw [List.mem_toFinset, rcR_keysN_mem e D rows dI rlab hdI hrl, Finset.mem_map]
  rfl

include hdI hrl in
theorem rcR_keysN_length :
    (rcRKeysN (rcRL dI) (rcRL rlab) k).length = (rcRKeys e D rows).card := by
  rw [← List.toFinset_card_of_nodup (rcR_keysN_pw dI rlab).nodup,
    rcR_keysN_toFinset e D rows dI rlab hdI hrl, Finset.card_map]

include hdI hrl in
/-- The index of a key in the program's list is its rank. -/
theorem rcR_findIdx_key {t : Fin k} (ht : t ∈ rcRKeys e D rows) :
    (rcRKeysN (rcRL dI) (rcRL rlab) k).findIdx (fun s => s == (t : ℕ)) = rcRRank e D rows t := by
  classical
  rw [rcR_findIdx_sorted (rcR_keysN_pw dI rlab)
    ((rcR_keysN_mem e D rows dI rlab hdI hrl).2 ⟨t, ht, rfl⟩), rcRRank]
  rw [← List.toFinset_card_of_nodup ((rcR_keysN_pw dI rlab).nodup.filter _)]
  rw [show ((rcRKeysN (rcRL dI) (rcRL rlab) k).filter fun s => decide (s < (t : ℕ))).toFinset =
    ((rcRKeys e D rows).filter (· < t)).map Fin.valEmbedding from ?_, Finset.card_map]
  ext j
  rw [List.mem_toFinset, List.mem_filter, rcR_keysN_mem e D rows dI rlab hdI hrl, Finset.mem_map]
  simp only [Finset.mem_filter, Fin.valEmbedding_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hlt⟩; exact ⟨s, ⟨hs, hlt⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hlt⟩, rfl⟩; exact ⟨⟨s, hs, rfl⟩, hlt⟩

variable {G : Subgroup (Perm Ω)} {m : ℕ} {c : Setoid Ω} {row' : Ω → Fin m}
  {ρ' : G →* alternatingGroup (Fin m)} (hs : CarrierSpec G D m rows c row' ρ') (hm : 0 < m)

include hdI hrl hs in
/-- **The program's row number is `rcRRow`.** -/
theorem rcR_rowN_eq {v : Ω} (hv : v ∈ D) :
    rcRRowN' (rcRL dI) (rcRL rlab) k (e v) = (rcRRow e D rows hm v : ℕ) := by
  unfold rcRRowN'
  rw [rcR_keyN_eq e D rows dI rlab hdI hrl hv,
    rcR_findIdx_key e D rows dI rlab hdI hrl (rcR_key_mem_keys hv), rcR_row_val hs hv hm]

include hdI hrl hs in
/-- **The program's row action is `ρ`.** -/
theorem rcR_rhoL_eq (hD : ∀ g ∈ G, ∀ v ∈ D, g v ∈ D) (g : G) {h : ℕ → ℕ}
    (hh : ∀ v : Fin k, h v = e ((g : Perm Ω) (e.symm v))) :
    rcRRhoL (rcRL dI) (rcRL rlab) k m h =
      (List.finRange m).map fun r => (((rcRRho e hs hm g : alternatingGroup (Fin m)) :
        Perm (Fin m)) r : ℕ) := by
  have hlen := rcR_keysN_length e D rows dI rlab hdI hrl
  rw [rcR_keys_card hs] at hlen
  unfold rcRRhoL
  have hfr : (List.finRange m).map Fin.val = List.range m := List.ext_getElem (by simp) (by simp)
  rw [← hfr, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  have hr : (r : ℕ) < (rcRKeysN (rcRL dI) (rcRL rlab) k).length := by rw [hlen]; exact r.2
  rw [List.getD_eq_getElem _ _ hr]
  have hmem := List.getElem_mem hr
  obtain ⟨t, ht, hte⟩ := (rcR_keysN_mem e D rows dI rlab hdI hrl).1 hmem
  obtain ⟨w, hw, hwt⟩ := rcR_mem_keys.1 ht
  have hvD := (rcR_key_rel (e := e) (rows := rows) hw).1
  set v := e.symm (rcRKey e D rows w)
  -- the row of the `r`-th key is `r`
  have hrow : (rcRRow e D rows hm v : ℕ) = r := by
    rw [← rcR_rowN_eq e D rows dI rlab hdI hrl hs hm hvD]
    unfold rcRRowN'
    rw [rcR_keyN_eq e D rows dI rlab hdI hrl hvD, rcR_key_key hw, hwt, hte]
    have hlt : (rcRKeysN (rcRL dI) (rcRL rlab) k).findIdx
        (fun s => s == (rcRKeysN (rcRL dI) (rcRL rlab) k)[(r : ℕ)]) <
        (rcRKeysN (rcRL dI) (rcRL rlab) k).length :=
      List.findIdx_lt_length_of_exists ⟨_, hmem, beq_self_eq_true _⟩
    have hp := List.findIdx_getElem (w := hlt)
    rw [beq_iff_eq] at hp
    exact ((rcR_keysN_pw dI rlab).nodup.getElem_inj_iff).1 hp
  have hgv : (g : Perm Ω) v ∈ D := hD g g.2 v hvD
  have he : h ((rcRKeysN (rcRL dI) (rcRL rlab) k)[(r : ℕ)]) = (e ((g : Perm Ω) v) : ℕ) := by
    rw [← hte, ← hwt]
    have := hh (rcRKey e D rows w)
    exact this
  rw [he, rcR_rowN_eq e D rows dI rlab hdI hrl hs hm hgv,
    (rcR_carrierSpec hs hm hD).row_equivariant g v hvD]
  congr 2
  exact Fin.ext hrow

end Rows

end GI.Impl
