module

public import Workspace.Impl.TermRecProgProfs

@[expose] public section

/-!
# T5, the class representatives of the profiles (item 3')

The program forms the profile of a piece `S` with the first piece `P_r` of its list that has
`Iso_H(P_r, S) ≠ ∅` (`TmRiProfOut`). This file turns that choice into the representatives of
`TermRecProgMath.lean`, and identifies the program's lists with the multisets of the proof.

* `tmRiPcsO`: the pieces of a list of objects, as lists of objects, in the program's order.
  Their values are the output of the pieces function (`tmRiPcsO_val`), their multisets are the
  pieces `pieces A X` (`tmRiPcsO_ms`, by `tmRiPcs_eq`), and each is a piece as the table needs
  (`tmRiPcsO_pc`).
* `tmRiCol`, `tmRiRepM`: the color of a multiset `S` is the first `r` with
  `Iso_H(P_r, S) ≠ ∅`, and its representative is `P_r`. They meet `TmRiRep` on the pieces
  (`tmRi_rep`).
* `tmRi_profs_ms`: the program's profiles are `tmRiProf` of these choices
  (`tmRec_prof_coset`); so the profile list of a side is `tmRiHat` (`tmRi_profs_hat`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {n : ℕ}

/-! ### Pieces of lists -/

section PcsList

variable {α β : Type}

/-- The default entry plays no role. -/
theorem tmRiPcs_congr_d (q : α → α → Bool) (L : List α) (d d' : α) {i : ℕ}
    (hi : i ≤ L.length) : tmRiPcs q L d i = tmRiPcs q L d' i := by
  have h : ∀ j ∈ List.range i, L.getD j d = L.getD j d' := fun j hj => by
    rw [List.mem_range] at hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < L.length by omega)]
  unfold tmRiPcs
  have e1 : (List.range i).filter (fun j => L.findIdx (q (L.getD j d)) == j) =
      (List.range i).filter (fun j => L.findIdx (q (L.getD j d')) == j) :=
    List.filter_congr (fun j hj => by rw [h j hj])
  rw [e1]
  exact List.map_congr_left (fun j hj => by rw [h j (List.mem_of_mem_filter hj)])

/-- The pieces of an image list are the images of the pieces. -/
theorem tmRiPcs_map (q : β → β → Bool) (f : α → β) (L : List α) (d : α) (i : ℕ) :
    tmRiPcs q (L.map f) (f d) i = (tmRiPcs (fun a b => q (f a) (f b)) L d i).map (List.map f) := by
  unfold tmRiPcs
  rw [List.map_map]
  simp only [List.getD_map, List.findIdx_map, List.filter_map]
  rfl

/-- A piece is the class of some entry. -/
theorem tmRiPcs_mem {q : α → α → Bool} {L : List α} {d : α} {i : ℕ} {Q : List α}
    (hQ : Q ∈ tmRiPcs q L d i) (hi : i ≤ L.length) :
    ∃ j, ∃ hj : j < L.length, Q = L.filter (q L[j]) := by
  unfold tmRiPcs at hQ
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hQ
  have hj' : j < L.length := by
    have := List.mem_range.1 (List.mem_of_mem_filter hj); omega
  refine ⟨j, hj', ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']

end PcsList

/-! ### Pieces of lists of objects -/

/-- The orbit test on objects. -/
noncomputable def tmRiQo (G : Subgroup (Perm (Fin n))) (o o' : TmRiO n) : Bool :=
  tmRiQ G (tmGlObjVal o) (tmGlObjVal o')

open Classical in
theorem tmRiQo_iff (G : Subgroup (Perm (Fin n))) (o o' : TmRiO n) :
    tmRiQo G o o' = true ↔ SameOrb G (tmRiObj o) (tmRiObj o') := by
  simp [tmRiQo, tmRiQ, tmRiDec_val]

/-- **The pieces of a list of objects**, as lists of objects, in the program's order. -/
noncomputable def tmRiPcsO (G : Subgroup (Perm (Fin n))) (X : List (TmRiO n)) :
    List (List (TmRiO n)) :=
  tmRiPcs (tmRiQo G) X (0, [], 1) X.length

/-- The values of the pieces are the output of the pieces function. -/
theorem tmRiPcsO_val (G : Subgroup (Perm (Fin n))) (X : List (TmRiO n)) :
    (tmRiPcsO G X).map tmGlObjsVal =
      (tmRiPcs (tmRiQ G) (X.map tmGlObjVal) (.nat 0) X.length).map Val.list := by
  rw [tmRiPcs_congr_d _ _ (.nat 0) (tmGlObjVal ((0, [], 1) : TmRiO n)) (by simp), tmRiPcs_map,
    List.map_map]
  rfl

theorem tmRiPcsO_length_le (G : Subgroup (Perm (Fin n))) (X : List (TmRiO n)) :
    (tmRiPcsO G X).length ≤ X.length := tmRiPcs_length_le _ _ _ _

/-- **The multisets of the pieces are the pieces** `pieces A X`, each once. -/
theorem tmRiPcsO_ms (G : Subgroup (Perm (Fin n))) (X : List (TmRiO n)) :
    ((((tmRiPcsO G X).map tmGlMs : List (Multiset (CObj ℕ (Perm (Fin n))))) :
      Multiset (Multiset (CObj ℕ (Perm (Fin n)))))) = (pieces G (tmGlMs X)).val :=
  tmRiPcs_eq G (fun o : TmRiO n => tmRiObj o) (tmRiQo G) (tmRiQo_iff G) X (0, [], 1)

theorem tmRiPcsO_mem {G : Subgroup (Perm (Fin n))} {X : List (TmRiO n)} {S : List (TmRiO n)}
    (hS : S ∈ tmRiPcsO G X) : ∃ o ∈ X, S = X.filter (tmRiQo G o) := by
  obtain ⟨j, hj, rfl⟩ := tmRiPcs_mem hS le_rfl
  exact ⟨X[j], List.getElem_mem hj, rfl⟩

theorem tmRi_ms_le_of_sublist {S X : List (TmRiO n)} (h : S.Sublist X) : tmGlMs S ≤ tmGlMs X :=
  Multiset.coe_le.2 (h.map _).subperm

/-- **Each piece is a piece as the table needs it**, and its objects are objects of the list. -/
theorem tmRiPcsO_pc {σA σN : List (Perm (Fin n))} {M : ℕ} {X : List (TmRiO n)}
    (hX : X.length ≤ M) (hN : Fixes (gens σN) (tmGlMs X)) {S : List (TmRiO n)}
    (hS : S ∈ tmRiPcsO (gens σA) X) : TmRiPc σA σN M S ∧ ∀ o ∈ S, o ∈ X := by
  obtain ⟨o, ho, rfl⟩ := tmRiPcsO_mem hS
  have hsub : (X.filter (tmRiQo (gens σA) o)).Sublist X := List.filter_sublist
  have horb : ∀ s ∈ tmGlMs (X.filter (tmRiQo (gens σA) o)),
      SameOrb (gens σA) (tmRiObj o) s := by
    intro s hs
    simp only [tmGlMs, Multiset.mem_coe, List.mem_map] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    exact (tmRiQo_iff _ _ _).1 (List.mem_filter.1 ha).2
  refine ⟨⟨?_, (List.length_filter_le _ _).trans hX, ?_, hN.of_le (tmRi_ms_le_of_sublist hsub)⟩,
    fun o' ho' => hsub.subset ho'⟩
  · apply List.ne_nil_of_mem (a := o)
    exact List.mem_filter.2 ⟨ho, (tmRiQo_iff _ _ _).2 (sameOrb_refl _ _)⟩
  · intro s hs s' hs'
    exact (horb s hs).symm.trans (horb s' hs')

/-! ### The representatives -/

section Rep

variable (H : Subgroup (Perm (Fin n))) (Ps : List (List (TmRiO n)))

open Classical in
/-- The color of a multiset: the first `r` with `Iso_H(P_r, S) ≠ ∅`. -/
noncomputable def tmRiCol (S : Multiset (CObj ℕ (Perm (Fin n)))) : ℕ :=
  Ps.findIdx fun R => decide (Iso H (tmGlMs R) S).Nonempty

/-- The representative of a multiset: the piece at its color. -/
noncomputable def tmRiRepM (S : Multiset (CObj ℕ (Perm (Fin n)))) :
    Multiset (CObj ℕ (Perm (Fin n))) :=
  tmGlMs (Ps.getD (tmRiCol H Ps S) [])

open Classical in
/-- The pieces of the list, as a finite set. -/
noncomputable def tmRiPF : Finset (Multiset (CObj ℕ (Perm (Fin n)))) := (Ps.map tmGlMs).toFinset

variable {H Ps}

/-- Two multisets in one `H`-class have the same color. -/
theorem tmRiCol_eq {S S' : Multiset (CObj ℕ (Perm (Fin n)))} (h : (Iso H S S').Nonempty) :
    tmRiCol H Ps S = tmRiCol H Ps S' := by
  obtain ⟨g, hg⟩ := h
  unfold tmRiCol
  congr 1
  funext R
  refine decide_eq_decide.2 ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩; exact ⟨x * g, iso_comp hx hg⟩
  · rintro ⟨x, hx⟩; exact ⟨x * g⁻¹, iso_comp hx (iso_inv hg)⟩

open Classical in
/-- On a piece, the color is a position, and its piece reaches `S`. -/
theorem tmRiCol_spec {S : Multiset (CObj ℕ (Perm (Fin n)))} (hS : S ∈ tmRiPF Ps) :
    tmRiCol H Ps S < Ps.length ∧ (Iso H (tmRiRepM H Ps S) S).Nonempty := by
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hS)
  have hex : ∃ x ∈ Ps, decide (Iso H (tmGlMs x) (tmGlMs R)).Nonempty = true :=
    ⟨R, hR, decide_eq_true ⟨1, H.one_mem, act_one _⟩⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  refine ⟨hlt, ?_⟩
  have h1 := List.findIdx_getElem (w := hlt)
  unfold tmRiRepM tmRiCol
  rw [List.getD_eq_getElem _ _ hlt]
  exact of_decide_eq_true h1

/-- **The first representative meets `TmRiRep`** on the pieces. -/
theorem tmRi_rep : TmRiRep H (tmRiPF Ps) (tmRiCol H Ps) (tmRiRepM H Ps) where
  nonempty S hS := (tmRiCol_spec hS).2
  rep_eq S _ S' _ h := by unfold tmRiRepM; rw [tmRiCol_eq h]
  col_iff S hS S' hS' := by
    constructor
    · intro he
      obtain ⟨g, hg⟩ := (tmRiCol_spec (H := H) hS).2
      obtain ⟨g', hg'⟩ := (tmRiCol_spec (H := H) hS').2
      unfold tmRiRepM at hg hg'
      rw [he] at hg
      exact ⟨g⁻¹ * g', iso_comp (iso_inv hg) hg'⟩
    · exact tmRiCol_eq

end Rep

/-! ### The profiles of the program are `tmRiProf` -/

open Classical in
/-- **One profile of the program** is the profile `tmRiProf` of the first representative. -/
theorem tmRi_profOut_obj {H A : Subgroup (Perm (Fin n))} (hAn : GI.Multicoset.Normalizes H A)
    {Ps : List (List (TmRiO n))} {j : ℕ} {ob : TmRiO n} (h : TmRiProfOut H A Ps j ob) :
    tmRiObj ob = tmRiProf H A (tmRiCol H Ps) (tmRiRepM H Ps) (tmGlMs (Ps.getD j [])) := by
  obtain ⟨hlt, hne, hfirst, hgens, -, ht⟩ := h
  have hcol : tmRiCol H Ps (tmGlMs (Ps.getD j [])) = ob.1 := by
    unfold tmRiCol
    rw [List.findIdx_eq hlt]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← List.getD_eq_getElem _ []]; exact decide_eq_true hne
    · rw [← List.getD_eq_getElem _ [], hfirst k hk]
      exact decide_eq_false Set.not_nonempty_empty
  have hrep : tmRiRepM H Ps (tmGlMs (Ps.getD j [])) = tmGlMs (Ps.getD ob.1 []) := by
    unfold tmRiRepM; rw [hcol]
  apply CObj.ext
  · exact hcol.symm
  · simp only [tmRiProf, tmGlObj, hrep]
    rw [tmRec_prof_coset hAn ht, hgens]

/-- **The profiles of `m` pieces from position `o`** form the multiset of `tmRiProf` of these
pieces. -/
theorem tmRi_profs_ms {H A : Subgroup (Perm (Fin n))} (hAn : GI.Multicoset.Normalizes H A)
    {Ps : List (List (TmRiO n))} {o m : ℕ} (hm : o + m ≤ Ps.length) {obs : List (TmRiO n)}
    (hl : obs.length = m) (hP : ∀ i (hi : i < obs.length), TmRiProfOut H A Ps (o + i) obs[i]) :
    tmGlMs obs = (((((Ps.drop o).take m).map tmGlMs : List (Multiset (CObj ℕ (Perm (Fin n))))) :
      Multiset (Multiset (CObj ℕ (Perm (Fin n)))))).map
        (tmRiProf H A (tmRiCol H Ps) (tmRiRepM H Ps)) := by
  rw [Multiset.map_coe]
  unfold tmGlMs
  congr 1
  apply List.ext_getElem
  · simp [hl]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [List.length_map] at h1
    have e := tmRi_profOut_obj hAn (hP i h1)
    rw [List.getD_eq_getElem _ _ (by omega)] at e
    exact e

/-- The pieces of both sides, `X` first. -/
noncomputable def tmRiPs (G : Subgroup (Perm (Fin n))) (X Y : List (TmRiO n)) :
    List (List (TmRiO n)) :=
  tmRiPcsO G X ++ tmRiPcsO G Y

theorem tmRiPs_length_le (G : Subgroup (Perm (Fin n))) (X Y : List (TmRiO n)) :
    (tmRiPs G X Y).length ≤ X.length + Y.length := by
  have := tmRiPcsO_length_le G X
  have := tmRiPcsO_length_le G Y
  simp only [tmRiPs, List.length_append]
  omega

theorem tmRiPs_sub_left (G : Subgroup (Perm (Fin n))) (X Y : List (TmRiO n)) :
    pieces G (tmGlMs X) ⊆ tmRiPF (tmRiPs G X Y) := by
  classical
  intro S hS
  have : S ∈ (pieces G (tmGlMs X)).val := hS
  rw [← tmRiPcsO_ms, Multiset.mem_coe] at this
  exact List.mem_toFinset.2 (by simp only [tmRiPs, List.map_append]; exact List.mem_append_left _ this)

theorem tmRiPs_sub_right (G : Subgroup (Perm (Fin n))) (X Y : List (TmRiO n)) :
    pieces G (tmGlMs Y) ⊆ tmRiPF (tmRiPs G X Y) := by
  classical
  intro S hS
  have : S ∈ (pieces G (tmGlMs Y)).val := hS
  rw [← tmRiPcsO_ms, Multiset.mem_coe] at this
  exact List.mem_toFinset.2 (by simp only [tmRiPs, List.map_append]; exact List.mem_append_right _ this)

/-- **The profiles of `X`** (positions `0, …, |P_X| - 1`) are `tmRiHat` of `X`. -/
theorem tmRi_profs_hat_left {H A : Subgroup (Perm (Fin n))} (hAn : GI.Multicoset.Normalizes H A)
    (X Y : List (TmRiO n)) {obs : List (TmRiO n)} (hl : obs.length = (tmRiPcsO A X).length)
    (hP : ∀ i (hi : i < obs.length), TmRiProfOut H A (tmRiPs A X Y) (0 + i) obs[i]) :
    tmGlMs obs = tmRiHat H A (tmRiCol H (tmRiPs A X Y)) (tmRiRepM H (tmRiPs A X Y)) (tmGlMs X) := by
  rw [tmRi_profs_ms hAn (by simp [tmRiPs]) hl hP]
  unfold tmRiHat
  rw [← tmRiPcsO_ms A X]
  simp [tmRiPs]

/-- **The profiles of `Y`** (positions `|P_X|, …`) are `tmRiHat` of `Y`. -/
theorem tmRi_profs_hat_right {H A : Subgroup (Perm (Fin n))} (hAn : GI.Multicoset.Normalizes H A)
    (X Y : List (TmRiO n)) {obs : List (TmRiO n)} (hl : obs.length = (tmRiPcsO A Y).length)
    (hP : ∀ i (hi : i < obs.length),
      TmRiProfOut H A (tmRiPs A X Y) ((tmRiPcsO A X).length + i) obs[i]) :
    tmGlMs obs = tmRiHat H A (tmRiCol H (tmRiPs A X Y)) (tmRiRepM H (tmRiPs A X Y)) (tmGlMs Y) := by
  rw [tmRi_profs_ms hAn (by simp [tmRiPs]) hl hP]
  unfold tmRiHat
  rw [← tmRiPcsO_ms A Y]
  simp [tmRiPs]

/-- The profiles are well formed objects for the recursive call: at most `n²` generators,
colors below `2M`, one subgroup per color. -/
theorem tmRi_profs_ok {H A : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))} {M : ℕ}
    (hPs : Ps.length ≤ 2 * M) {obs : List (TmRiO n)}
    (hP : ∀ ob ∈ obs, ∃ j, TmRiProfOut H A Ps j ob) : TmRecObjOK M obs := by
  intro o ho
  obtain ⟨j, hj⟩ := hP o ho
  refine ⟨hj.2.2.2.2.1, by have := hj.1; omega, fun o' ho' he => ?_⟩
  obtain ⟨j', hj'⟩ := hP o' ho'
  rw [hj.2.2.2.1, hj'.2.2.2.1, he]

theorem tmRi_profs_mem {H A : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))} {o : ℕ}
    {obs : List (TmRiO n)} (hP : ∀ i (hi : i < obs.length), TmRiProfOut H A Ps (o + i) obs[i]) :
    ∀ ob ∈ obs, ∃ j, TmRiProfOut H A Ps j ob := by
  intro ob hob
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hob
  exact ⟨_, hP i hi⟩

theorem tmRi_profs_in {H A : Subgroup (Perm (Fin n))} (hAH : A ≤ H)
    {Ps : List (List (TmRiO n))} {obs : List (TmRiO n)}
    (hP : ∀ ob ∈ obs, ∃ j, TmRiProfOut H A Ps j ob) : TmRiListIn H obs := by
  intro o ho
  obtain ⟨j, hj⟩ := hP o ho
  refine tmRiStab_le_of ?_ hj.2.2.2.2.2.1
  rw [hj.2.2.2.1]
  exact sup_le hAH (aut_le H _)

/-- **A transporter written from the other side**: `Iso_H(Y, X) = v K` gives
`Iso_H(X, Y) = K v⁻¹`. -/
theorem tmRi_iso_swap {G : Type} [Group G] {Ω : Type} [RAct G Ω] {H : Subgroup G} {X Y : Ω}
    {v : G} {K : Subgroup G} (h : Iso H Y X = v • (K : Set G)) :
    Iso H X Y = tmGlCoset K v⁻¹ := by
  ext g
  rw [tmRi_mem_iso_inv, h]
  simp only [tmGlCoset, Set.mem_smul_set, Set.mem_image, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨k⁻¹, K.inv_mem hk, by rw [← mul_inv_rev, he, inv_inv]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k⁻¹, K.inv_mem hk, by group⟩

end GI.Impl
