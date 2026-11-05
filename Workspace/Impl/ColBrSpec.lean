module

public import Workspace.Impl.ColBrDet
public import Workspace.Impl.ColSpec
public import Workspace.Impl.RowSpecTerm
public import Workspace.Impl.RowThr

@[expose] public section

/-!
# The column branch: linking the program values to the state

This file connects the hypotheses of `colChild_det` to the state and the row form.

* `colCf_inv`: the column coordinate of each position, read from the pure coordinates `E`, is
  the value of `colInvF` on the coordinate rows (`colRowsR`, the rows of `coordsVal`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

variable {Ω C : Type} {n m q : ℕ}

/-! ### The coordinate rows and the column coordinate -/

/-- The coordinate rows as lists of positions: row `j` lists `e (E (β, j))` for `β < m`. -/
def colRowsR (e : Ω ≃ Fin n) (S : State Ω C) (E : Fin m × Fin q ≃ S.dom) : List (List ℕ) :=
  (List.finRange q).map fun j => (List.finRange m).map fun β => ((e (E (β, j)).val : Fin n) : ℕ)

theorem colCoordsVal_eq (e : Ω ≃ Fin n) (S : State Ω C) {L : GiantLabels S}
    (E : Fin m × Fin L.q ≃ S.dom) :
    coordsVal e S E = .list ((colRowsR e S E).map natList) := by
  simp [coordsVal, colRowsR, List.map_map, Function.comp_def]

open Classical in
/-- The column coordinate of a position, `0` off the domain. -/
noncomputable def colCfOf (e : Ω ≃ Fin n) (S : State Ω C) (E : Fin m × Fin q ≃ S.dom)
    (h0 : 0 < m) (i : Fin n) : Fin m :=
  if h : e.symm i ∈ S.dom then (E.symm ⟨e.symm i, h⟩).1 else ⟨0, h0⟩

theorem colCfOf_dom (e : Ω ≃ Fin n) (S : State Ω C) (E : Fin m × Fin q ≃ S.dom) (h0 : 0 < m)
    (v : S.dom) : colCfOf e S E h0 (e v) = (E.symm v).1 := by
  unfold colCfOf
  rw [dif_pos (by simp)]
  congr 2
  ext; simp

/-- **The column coordinate is the value of `colInvF`.** -/
theorem colCf_inv (e : Ω ≃ Fin n) (S : State Ω C) {L : GiantLabels S}
    (E : Fin m × Fin L.q ≃ S.dom) (h0 : 0 < m)
    (label : Ω → Fin L.q) (hlab : ∀ b j, label (E (b, j)) = j) (rl : Fin n → ℕ)
    (hrl : ∀ i, e.symm i ∈ S.dom → rl i = label (e.symm i)) (i : Fin n) :
    (colCfOf e S E h0 i : ℕ) = colInvv (colRowsR e S E) (indF e S.dom) rl i := by
  unfold colInvv indF
  by_cases h : e.symm i ∈ S.dom
  · rw [if_neg (by simp [h])]
    set v : S.dom := ⟨e.symm i, h⟩ with hv
    have hi : e v = i := by simp [hv]
    rcases hE : E.symm v with ⟨β, j⟩
    have hEv : E (β, j) = v := by rw [← hE]; simp
    have hc : colCfOf e S E h0 i = β := by
      rw [← hi, colCfOf_dom, hE]
    have hrj : rl i = j := by
      rw [hrl i h, show e.symm i = (E (β, j) : Ω) by rw [hEv], hlab]
    have hj : (j : ℕ) < (colRowsR e S E).length := by simp [colRowsR]
    rw [hc, hrj, List.getD_eq_getElem _ _ hj]
    have hrow : (colRowsR e S E)[(j : ℕ)] = (rowList e E j).map Fin.val := by
      simp [colRowsR, rowList, List.map_map, Function.comp_def]
    have hiv : (i : ℕ) = (e (E (β, j)) : ℕ) := by rw [hEv, hi]
    rw [hrow, hiv, findIdx_rowList]
  · rw [if_pos (by simp [h])]
    unfold colCfOf
    rw [dif_neg h]

/-! ### Reading the hierarchy value -/

/-- **The stored hierarchy as the program reads it**: a canonical hierarchy value is `colHV` of
some labels of its levels and of the stored ratios, bounds and origins. -/
theorem colHier_read {k : ℕ} {e : Ω ≃ Fin k} {hv : Val} {l : List (Interval Ω)}
    (h : HierValC e hv l) :
    ∃ labs : ℕ → Fin k → ℕ,
      hv = colHV (fun j : Fin l.length => labs j) (fun j => l[j].ratio) (fun j => l[j].cap)
        (fun j => l[j].origin) ∧
      (∀ j (hj : j < l.length) i i', labs j i = labs j i' ↔ (l[j]).part.r (e.symm i) (e.symm i')) ∧
      ∀ j i, labs j i < k := by
  obtain ⟨vs, rfl, h2⟩ := h
  induction h2 with
  | nil =>
    refine ⟨fun _ _ => 0, by simp [colHV], fun j hj => by simp at hj, fun j i => ?_⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  | @cons a I vs l hab _ ih =>
    obtain ⟨labs', hv', hl', hb'⟩ := ih
    obtain ⟨pv, ⟨lab, rfl, hlt, hR⟩, rfl⟩ := hab
    refine ⟨fun j => if j = 0 then lab else labs' (j - 1), ?_, fun j hj i i' => ?_, fun j i => ?_⟩
    · simp only [colHV, Val.list.injEq] at hv' ⊢
      simp [List.finRange_succ, List.map_map, Function.comp_def, hv']
    · rcases j with _ | j
      · simpa using hR i i'
      · simpa using hl' j (by simpa using hj) i i'
    · dsimp only
      split_ifs
      · exact hlt i
      · exact hb' _ i

/-! ### The switch -/

theorem colIndF_ne_zero {k : ℕ} (e : Ω ≃ Fin k) (D : Set Ω) (i : Fin k) :
    indF e D i ≠ 0 ↔ e.symm i ∈ D := by
  unfold indF; split_ifs with h <;> simp [h]

/-- **The switch that the program finds.** The first stored level whose next level does not
refine the rows is a switch: level `J` refines the rows and level `J + 1` meets every row. -/
theorem colSwitch_find {k : ℕ} {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (e : Ω ≃ Fin k)
    (labs : ℕ → Fin k → ℕ)
    (hlabs : ∀ j (hj : j < S.hier.length) i i', labs j i = labs j i' ↔
      (S.hier[j]).part.r (e.symm i) (e.symm i'))
    (rl : Fin k → ℕ) (hrl : ∀ i, e.symm i ∈ S.dom → rl i = (F.label (e.symm i) : ℕ))
    (p00 : Fin k) (hp0 : e.symm p00 ∈ S.dom) (hp0r : (F.label (e.symm p00) : ℕ) = 0) :
    ∃ J : Fin S.hier.length,
      ((List.finRange S.hier.length).map (colNotLowv (fun j : Fin S.hier.length => labs j)
        (indF e S.dom) rl p00)).findIdx (fun x => decide (x = 1)) = J ∧
      F.Low (levOf ⊥ S.hier J) ∧ F.High (levOf ⊥ S.hier (J + 1)) := by
  have hinv' : HierInv S.G S.dom S.hier := hinv
  have hl : 0 < S.hier.length := F.hier_pos htr hinv hne
  have hval : ∀ j : Fin S.hier.length, colNotLowv (fun j : Fin S.hier.length => labs j)
      (indF e S.dom) rl p00 j = 0 ↔ F.Low (levOf ⊥ S.hier (j + 1)) := by
    intro j
    rw [levOf_succ_of_lt j.2]
    refine colNotLowv_eq_zero_iff F htr e _ j ?_ _ rl (hlabs j j.2) (colIndF_ne_zero e S.dom)
      hrl p00 hp0 hp0r
    have := levOf_inv hinv' (j + 1)
    rwa [levOf_succ_of_lt j.2] at this
  have hle : ∀ j, colNotLowv (fun j : Fin S.hier.length => labs j) (indF e S.dom) rl p00 j ≠ 0 →
      colNotLowv (fun j : Fin S.hier.length => labs j) (indF e S.dom) rl p00 j = 1 := by
    intro j; unfold colNotLowv; split_ifs <;> simp
  set lst := (List.finRange S.hier.length).map (colNotLowv (fun j : Fin S.hier.length => labs j)
    (indF e S.dom) rl p00) with hlst
  have hlen : lst.length = S.hier.length := by simp [hlst]
  have hex : ∃ x ∈ lst, decide (x = 1) = true := by
    refine ⟨colNotLowv (fun j : Fin S.hier.length => labs j) (indF e S.dom) rl p00
      ⟨S.hier.length - 1, by omega⟩, List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩, ?_⟩
    refine decide_eq_true (hle _ fun h0 => ?_)
    have := (hval _).1 h0
    have h1 : (S.hier.length - 1 : ℕ) + 1 = S.hier.length := by omega
    simp only [h1] at this
    exact Col.colLast_not_low F htr hinv hl hne this
  have hJlt := List.findIdx_lt_length_of_exists hex
  refine ⟨⟨_, hlen ▸ hJlt⟩, rfl, ?_⟩
  refine Col.colSwitch_of_first F htr hinv (fun j hj => ?_) ?_
  · have hj' : j < S.hier.length := by omega
    have h1 := List.not_of_lt_findIdx hj
    have h2 : colNotLowv (fun j : Fin S.hier.length => labs j) (indF e S.dom) rl p00
        ⟨j, hj'⟩ ≠ 1 := by simpa [hlst] using h1
    exact (hval ⟨j, hj'⟩).1 (by by_contra h3; exact h2 (hle _ h3))
  · intro hlow
    have h1 := List.findIdx_getElem (w := hJlt)
    have h2 : colNotLowv (fun j : Fin S.hier.length => labs j) (indF e S.dom) rl p00
        ⟨_, hlen ▸ hJlt⟩ = 1 := by simpa [hlst] using h1
    have h0 := (hval ⟨_, hlen ▸ hJlt⟩).2 hlow
    exact absurd (h2.symm.trans h0) (by norm_num)

/-! ### The child hierarchy in the program's form -/

theorem colOfFn_eq {α β : Type} (l : List α) {len : ℕ} (h : l.length = len) (f : ℕ → α → β)
    (g : Fin len → β) (hfg : ∀ k : Fin len, f k (l[(k : ℕ)]'(h ▸ k.2)) = g k) :
    List.ofFn (fun k : Fin l.length => f k l[(k : ℕ)]) = (List.finRange len).map g := by
  subst h
  apply List.ext_getElem <;> simp [hfg]

section Child

variable {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

set_option backward.isDefEq.respectTransparency false in
/-- **The child hierarchy value, in the form the program computes** (`colHierL`, with the
stored bounds and origins). -/
theorem colChild_hierVal' [Finite Ω] (hnat : NaturalRows S L label) (hq : 5 ≤ L.q)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E) (h0 : 0 < m)
    (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (J : Fin S.hier.length)
    (hlowJ : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Low (levOf ⊥ S.hier J))
    (hhighJ : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).High (levOf ⊥ S.hier (J + 1)))
    (eΩ : Ω ≃ Fin n) (labs : ℕ → Fin n → ℕ)
    (hlabs : ∀ k (hk : k < S.hier.length) i j, labs k i = labs k j ↔
      (S.hier[k]'hk).part.r (eΩ.symm i) (eΩ.symm j))
    (hlabn : ∀ k i, labs k i < n + 1)
    (r0 : Fin m → Fin n)
    (hr0 : ∀ c, r0 c = eΩ ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e
      (c, (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).i0)))
    (ol : Fin m → ℕ)
    (hol : ∀ c d : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B, ol c = ol d ↔
      ∃ x : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl,
        (x : (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb) • c = d)
    (holn : ∀ c, ol c < n + 1)
    (cf : Fin n → Fin m)
    (hcol : ∀ v : S.dom, cf (eΩ v) = ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e.symm v).1)
    (rlf : Fin n → ℕ)
    (hrl : ∀ v : S.dom, rlf (eΩ v) = ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).label v : ℕ)) :
    HierValC eΩ (.list ((colHierL labs (fun j : Fin S.hier.length => S.hier[j].cap)
        (fun j : Fin S.hier.length => S.hier[j].origin) r0 ol cf rlf (indF eΩ S.dom) h0 L.q
        J).filter colKeep))
      (dropTriv (Col.colStep (RowForm.ofPure hnat hq E hP ⟨0, h0⟩) hint htr hinv hne ⟨0, h0⟩ J
        J.2 hlowJ hhighJ).hier') := by
  have H := colChild_hierVal hnat hq E hP ⟨0, h0⟩ hint htr hinv hne h0 J J.2 hlowJ hhighJ eΩ labs
    hlabs hlabn r0 hr0 ol hol holn cf hcol rlf hrl
  convert H using 4
  have hlen : (Col.colStep (RowForm.ofPure hnat hq E hP ⟨0, h0⟩) hint htr hinv hne ⟨0, h0⟩ J
      J.2 hlowJ hhighJ).loc.length = S.hier.length := by
    show ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).expLoc _).length = _
    simp
  unfold colHierL
  congr 1
  congr 1
  · symm
    refine colOfFn_eq _ hlen (fun k x => colIV (colLowLab labs ol cf rlf (indF eΩ S.dom) k)
      (colLowRat labs r0 ol h0 k) (min x.cap (colLowRat labs r0 ol h0 k)) x.origin) _ fun k => ?_
    show colIV _ _ (min ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).expLoc _)[(k : ℕ)].cap _)
      ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).expLoc _)[(k : ℕ)].origin = _
    simp [RowForm.expLoc, colLowVal]
  · symm
    refine colOfFn_eq _ hlen (fun k x => colIV (colUpLab labs r0 ol cf (indF eΩ S.dom) k)
      (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
      (min x.cap (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)) x.origin) _ fun k => ?_
    show colIV _ _ (min ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).expLoc _)[(k : ℕ)].cap _)
      ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).expLoc _)[(k : ℕ)].origin = _
    simp [RowForm.expLoc, colUpVal]

end Child

/-! ### The numbers of the child hierarchy -/

theorem colImage_ncard_le {m : ℕ} (A : Fin m → ℕ) (s : Set (Fin m)) : (A '' s).ncard ≤ m := by
  refine (Set.ncard_image_le (Set.toFinite s)).trans ?_
  refine (Set.ncard_le_ncard (Set.subset_univ s)).trans ?_
  simp [Set.ncard_univ]

theorem colRat_le (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (h0 : 0 < m) (k : ℕ) :
    colRat labs r0 h0 k ≤ m := by
  unfold colRat; rw [colCount']; exact colImage_ncard_le _ _

theorem colLowRat_le (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (ol : Fin m → ℕ) (h0 : 0 < m)
    (k : ℕ) : colLowRat labs r0 ol h0 k ≤ m := by
  unfold colLowRat; rw [colCount']; exact colImage_ncard_le _ _

/-- **The numbers of the program's hierarchy are small**: every interval value of `colHierL` has
ratio, bound and origin at most `B` when the stored bounds and origins, `m` and `q` are. -/
theorem colHierL_bound {len B : ℕ} (labs : ℕ → Fin n → ℕ) (caps origs : Fin len → ℕ)
    (r0 : Fin m → Fin n) (ol : Fin m → ℕ) (cf : Fin n → Fin m) (rl dv : Fin n → ℕ) (h0 : 0 < m)
    (J : Fin len) (horig : ∀ k, origs k ≤ B) (hm : m ≤ B) (hq : q ≤ B) :
    ∀ v ∈ colHierL labs caps origs r0 ol cf rl dv h0 q J, ∃ (lab : Fin n → ℕ) (r c o : ℕ),
      v = colIV lab r c o ∧ r ≤ B ∧ c ≤ B ∧ o ≤ B := by
  intro v hv
  simp only [colHierL, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_singleton] at hv
  rcases hv with (⟨k, rfl⟩ | rfl) | ⟨k, rfl⟩
  · have := colLowRat_le labs r0 ol h0 k
    exact ⟨_, _, _, _, rfl, by omega, (min_le_right _ _).trans (by omega), horig k⟩
  · exact ⟨_, _, _, _, rfl, hq, (min_le_right _ _).trans hq, horig J⟩
  · have := colRat_le labs r0 h0 k
    have := Nat.div_le_self (colRat labs r0 h0 k) (colLowRat labs r0 ol h0 k)
    exact ⟨_, _, _, _, rfl, by omega, (min_le_right _ _).trans (by omega), horig k⟩

theorem colForall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := colForall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- **The child intervals are nontrivial with small numbers**, read from their values. -/
theorem colIntervalsOK {k B : ℕ} {e : Ω ≃ Fin k} {vs : List Val} {l : List (Interval Ω)}
    (h : HierValC e (.list (vs.filter colKeep)) l)
    (hvs : ∀ v ∈ vs, ∃ (lab : Fin k → ℕ) (r c o : ℕ), v = colIV lab r c o ∧ r ≤ B ∧ c ≤ B ∧ o ≤ B) :
    IntervalsOK B l := by
  obtain ⟨ws, hws, h2⟩ := h
  injection hws with hws
  subst hws
  intro I hI
  obtain ⟨v, hv, hvI⟩ := colForall₂_mem_right h2 I hI
  obtain ⟨hv1, hv2⟩ := List.mem_filter.1 hv
  obtain ⟨lab, r, c, o, rfl, hr, hc, ho⟩ := hvs v hv1
  obtain ⟨pv, -, he⟩ := hvI
  simp only [colIV, Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at he
  obtain ⟨-, rfl, rfl, rfl⟩ := he
  simp only [colKeep, colIV, decide_eq_true_eq] at hv2
  exact ⟨hv2, hr, hc, ho⟩

/-! ### The child state -/

/-- **The child of the column step** (`Run.rowColumns`, as in the giant `.columns` case of
`Workspace/Algorithm/Existence.lean`): the same core, the hierarchy `dropTriv I.hier'`, the row
record `⟨q, rowPart, some cols⟩`, `h - 1` and the same `N`. -/
noncomputable def colChildState [Finite Ω] (S : State Ω C) (L : SuppliedLabels S)
    (htr : S.Transitive) (hsN : S.size ≤ S.N) (hrow : RowCase P₀.α S L.toGiantLabels)
    (I : ColumnStep S L.toGiantLabels) : State Ω C :=
  ⟨S.G, S.dom, S.dom_inv, S.x, S.y, dropTriv I.hier', some ⟨L.q, I.rowPart, some I.cols⟩, S.floor,
    S.h - 1, by have := S.h_le; omega, S.N,
    (column_step_counter P₀_terminating.third_lt_α S htr hsN L.toGiantLabels hrow I).2,
    CarrierOK.dropTriv S.dom_inv htr (I.hierInv htr) I.carrierOK⟩

theorem colChildState_rho [Finite Ω] {S : State Ω C} {L : GiantLabels S} (I : ColumnStep S L) :
    rhoNat (dropTriv I.hier') ≤ rhoNat S.hier := by
  have h1 : (rhoNat (dropTriv I.hier') : ℝ) ≤ rhoNat S.hier := by
    rw [rhoNat_cast, rhoNat_cast, hierRho_dropTriv]; exact I.rho_le
  exact_mod_cast h1

theorem colChildState_good [Finite Ω] {S : State Ω C} {L : SuppliedLabels S}
    (hgood : Good P₀ .giant S) (htr : S.Transitive) (hsN : S.size ≤ S.N)
    (hrow : RowCase P₀.α S L.toGiantLabels) (I : ColumnStep S L.toGiantLabels) :
    Good P₀ .cont (colChildState S L htr hsN hrow I) :=
  ⟨hgood.1, hsN, HierInv.dropTriv S.dom_inv (I.hierInv htr)⟩

theorem colChildState_mlt [Finite Ω] {S : State Ω C} {L : SuppliedLabels S}
    (htr : S.Transitive) (hsN : S.size ≤ S.N)
    (hrow : RowCase P₀.α S L.toGiantLabels) (I : ColumnStep S L.toGiantLabels) :
    MLt (measure P₀ .cont (colChildState S L htr hsN hrow I)) (measure P₀ .giant S) := by
  obtain ⟨hh1, -⟩ := column_step_counter P₀_terminating.third_lt_α S htr hsN L.toGiantLabels hrow I
  have hρ := colChildState_rho I
  have htr' : trInd (colChildState S L htr hsN hrow I) = 1 := trInd_of _ htr
  have htr1 : trInd S = 1 := trInd_of S htr
  rw [mlt_iff]
  simp only [GI.Algorithm.measure, major, solveInd, stageInd, true_and, lt_self_iff_false, false_or]
  have h1 : (colChildState S L htr hsN hrow I).size = S.size := rfl
  have hNj : (colChildState S L htr hsN hrow I).N = S.N := rfl
  have h2 : (colChildState S L htr hsN hrow I).sigma P₀.κ = S.sigma P₀.κ := rfl
  have h3 : flInd (colChildState S L htr hsN hrow I) = flInd S := rfl
  have h4 : (colChildState S L htr hsN hrow I).h = S.h - 1 := rfl
  have h5 : rhoNat (colChildState S L htr hsN hrow I).hier = rhoNat (dropTriv I.hier') := rfl
  omega

/-! ### The column branch meets its specification -/

/-- The bound on the numbers and weights of the column branch, in the phase size `N`. -/
def colBrX (N : ℕ) : ℕ := 10 ^ 6 * (N + 2) ^ 6

/-- **The cost bound of the column branch** without the child call, in the phase size `N`. -/
def colBrPoly (N : ℕ) : ℕ :=
  16 * (orbitK * (4 * (N + 2) ^ 3) ^ 5) + 10 ^ 34 * (colBrX N + 1) ^ 6 + 1000 * (N + 2) ^ 6 + 1

theorem colBrX_ge (N : ℕ) : (N + 2) ^ 6 ≤ colBrX N :=
  Nat.le_mul_of_pos_left _ (by norm_num)

theorem colRowLab_dom {k : ℕ} (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) (hq : 5 ≤ L.q) {label : Ω → Fin L.q} (hn : NaturalRows S L label)
    (i : Fin k) (hi : e.symm i ∈ S.dom) : rowLab e J i = (label (e.symm i) : ℕ) :=
  rowLab_on e J hi (blocks_eq_label J hq hn ⟨_, hi⟩)

theorem colRowLab_le {k : ℕ} (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) (i : Fin k) : rowLab e J i ≤ L.q := by
  unfold rowLab
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))

/-- The weight of the input of the column branch. -/
theorem colBrIn_wt_le {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {sv : Val}
    {L : GiantLabels S} (hsv : Canon e c sv S) (J : JohnsonBlocks S L)
    (E : Fin m × Fin L.q ≃ S.dom) (hq : 0 < L.q) {σN : List (Perm (Fin m))}
    (hlN : σN.length ≤ (k + L.q) ^ 2) :
    (colBrIn sv L.q (colRowsR e S E) σN (rowLab e J)).wt ≤ colBrX S.N := by
  set P := S.N + 2 with hP
  have hk : k ≤ S.N := hsv.fits
  have hqk : L.q ≤ k + 2 := GiantLabels.q_le e L
  have hmk : m ≤ k := m_le_n e E ⟨0, hq⟩
  have p6 : P ^ 2 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : P ^ 3 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p16 : P ≤ P ^ 6 := Nat.le_self_pow (by norm_num) _
  have w1 : sv.wt ≤ 10 ^ 4 * P ^ 6 := hsv.wt_le_poly
  have w3 : (coordsVal e S E).wt ≤ 15 * (k + L.q + 2) ^ 3 + 4 := wt_coordsVal_le E
  have w3' : (coordsVal e S E).wt ≤ 200 * P ^ 6 := by
    have h1 := Nat.pow_le_pow_left (show k + L.q + 2 ≤ 2 * P by omega) 3
    have h2 : (2 * P) ^ 3 = 8 * P ^ 3 := by ring
    omega
  have w4 : (a18Out σN σN σN 0).wt ≤ 400 * (k + L.q + 1) ^ 6 + 20 := by
    have hM : (k + L.q) ^ 2 + 1 ≤ 2 * (k + L.q + 1) ^ 2 := by nlinarith
    exact wt_a18Out_le (by omega) (Nat.zero_le _) (by omega) (by omega) (by omega)
  have w4' : (Val.list (σN.map encPerm)).wt ≤ 30000 * P ^ 6 := by
    have h0 : (Val.list (σN.map encPerm)).wt < (a18Out σN σN σN 0).wt :=
      wt_le_wt_list (by simp)
    have h1 := Nat.pow_le_pow_left (show k + L.q + 1 ≤ 2 * P by omega) 6
    have h2 : (2 * P) ^ 6 = 64 * P ^ 6 := by ring
    omega
  have w5 : (encFun (rowLab e J)).wt ≤ 5 * (k + L.q + 1) ^ 2 :=
    wt_encFun_le' _ (fun i => (colRowLab_le e J i).trans (by omega)) (by omega)
  have w5' : (encFun (rowLab e J)).wt ≤ 20 * P ^ 6 := by
    have h1 := Nat.pow_le_pow_left (show k + L.q + 1 ≤ 2 * P by omega) 2
    have h2 : (2 * P) ^ 2 = 4 * P ^ 2 := by ring
    omega
  have w2 := wt_nat_le L.q
  have hR : Val.list ((colRowsR e S E).map natList) = coordsVal e S E :=
    (colCoordsVal_eq e S E).symm
  have := wt_list_le [sv, .nat L.q, .list ((colRowsR e S E).map natList),
    .list (σN.map encPerm), encFun (rowLab e J)]
  rw [hR] at this
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  show _ ≤ 10 ^ 6 * P ^ 6
  unfold colBrIn
  rw [hR]
  omega

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

set_option maxHeartbeats 1600000 in
/-- **The column branch meets its specification.** On the canonical state value `sv`, the
number of rows `q`, the coordinate rows of the pure coordinates `E` (`coordsVal`), generators
`σN` of `N` (from `a18_spec`) and the row labels, when `N` is not transitive on a row, the
function `b` of the module `colBrFuns b F.cont` returns a canonical answer of a run that starts
with `Run.rowColumns`, whose child is the call that the function makes, at cost at most
`colBrPoly N` plus the cost of the child. -/
theorem colBr_spec {b : ℕ} (hA : ColBrAt Pg b F.cont)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (hc : Function.Injective c) (sv : Val) (L : SuppliedLabels S) (hsv : Canon e c sv S)
    (hgood : Good P₀ .giant S) (hrow : RowCase P₀.α S L.toGiantLabels)
    (ih : I.IH Pg F .giant S)
    (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
    {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
    (hP : PureCoords S L.toGiantLabels label E) (σN : List (Perm (Fin m)))
    (hN : Subgroup.closure {σ | σ ∈ σN} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (hnt : ¬ MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hlN : σN.length ≤ (k + L.q) ^ 2) :
    FunAll Pg b (colBrIn sv L.q (colRowsR e S E) σN (rowLab e L.con.blocks))
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A),
        r.kind = .rowColumns ∧ AnsC e u A ∧ (cost : ℝ) ≤ (colBrPoly S.N : ℝ) + I.childCost r) := by
  classical
  have hgood0 := hgood
  obtain ⟨hN0, hsN, htr, hth, hhi, -⟩ := hgood
  have hq0 : 0 < L.q := by omega
  have hne : S.dom.Nonempty := ⟨(E (⟨0, h0⟩, ⟨0, hq0⟩)).1, (E _).2⟩
  have hkN : k ≤ S.N := hsv.fits
  have hmk : m ≤ k := m_le_n e E ⟨0, hq0⟩
  have hsize : S.size = m * L.q := by
    unfold State.size
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hqN : L.q ≤ S.N := by
    have : L.q ≤ m * L.q := Nat.le_mul_of_pos_left _ h0
    omega
  have hqk : L.q ≤ k := by
    have h1 : S.size ≤ Nat.card Ω := Finite.card_subtype_le _
    rw [card_eq e] at h1
    have : L.q ≤ m * L.q := Nat.le_mul_of_pos_left _ h0
    omega
  have hsmall := hsv.small'
  set Fm := RowForm.ofPure hnat hq E hP ⟨0, h0⟩ with hFm
  haveI : Nonempty Fm.B := ⟨(⟨0, h0⟩ : Fin m)⟩
  have hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel Fm.Nl Fm.B)) := Fm.two_le_orbits hnt
  -- the state value
  obtain ⟨gv, dv0, xv, yv, hv, rv, hg, hd, hx, hy, hh, hr, hsvE⟩ := hsv.val
  have hd' : dv0 = encFun (indF e S.dom) := hd
  subst hd'
  obtain ⟨labs, hhv, hlabs, hlabk⟩ := colHier_read hh
  -- the row labels, the orbit labels and the switch
  have hrlD : ∀ i, e.symm i ∈ S.dom → rowLab e L.con.blocks i = (label (e.symm i) : ℕ) :=
    fun i hi => colRowLab_dom e L.con.blocks hq hnat i hi
  obtain ⟨ol, hol, holr, holb⟩ := orbits_spec hA.orb σN
  have hol' := colOrbit_labels Fm (gs := σN) hN ol holr
  have holm : ∀ c, ol c < m := fun c => (holb c).1
  set r0 : Fin m → Fin k := fun c => e (E (c, ⟨0, hq0⟩)) with hr0
  obtain ⟨J, hJ, hlowJ, hhighJ⟩ := colSwitch_find Fm htr hhi hne e labs hlabs
    (rowLab e L.con.blocks) (fun i hi => hrlD i hi) (r0 ⟨0, h0⟩) (by simp [hr0])
    (by simp [hr0, hFm, RowForm.ofPure_label, hP.label_e])
  set Ic := Col.colStep Fm hint htr hhi hne ⟨0, h0⟩ J J.2 hlowJ hhighJ with hIc
  set cf := colCfOf e S E h0 with hcf
  have hcol : ∀ v : S.dom, cf (e v) = (Fm.e.symm v).1 := colCfOf_dom e S E h0
  have hrlv : ∀ v : S.dom, rowLab e L.con.blocks (e v) = (Fm.label v : ℕ) := fun v => by
    simpa [hFm, RowForm.ofPure_label] using hrlD (e v) (by simp)
  have hHV := colChild_hierVal' hnat hq E hP h0 hint htr hhi hne J hlowJ hhighJ e labs hlabs
    (fun j i => by have := hlabk j i; omega) r0 (fun c => rfl) ol hol'
    (fun c => by have := holm c; omega) cf hcol (rowLab e L.con.blocks) hrlv
  -- the child state and its canonical value
  set S' := colChildState S L htr hsN hrow Ic with hS'
  have horig : ∀ j : Fin S.hier.length, S.hier[j].origin ≤ S.N := fun j =>
    (hsmall.2.1 _ (List.getElem_mem _)).2.2
  have hIOK : IntervalsOK S.N (dropTriv Ic.hier') :=
    colIntervalsOK hHV (colHierL_bound labs _ _ r0 ol cf _ _ h0 J horig (by omega) hqN)
  have hrowP : PartitionValC e (encFun (rowLab e L.con.blocks)) Ic.rowPart :=
    rowPart_val e L.con.blocks hq hnat
  have hcolsP : PartitionValC e (encFun (colColsLab ol cf (indF e S.dom))) Ic.cols := by
    have := Col.colCols_val Fm hint htr hhi hne ⟨0, h0⟩ J J.2 hlowJ hhighJ e cf hcol ol hol'
    have hk : (fun i => ol (cf i) + k + 1) = fun i => ol (cf i) + (k + 1) := by
      funext i; omega
    rw [hk] at this
    exact this
  have hcan : Canon e c (colChildVal gv (indF e S.dom) (rowLab e L.con.blocks) xv yv
      (boolVal S.floor) S.h S.N L.q (colHierL labs (fun j : Fin S.hier.length => S.hier[j].cap)
        (fun j : Fin S.hier.length => S.hier[j].origin) r0 ol cf (rowLab e L.con.blocks)
        (indF e S.dom) h0 L.q J) (colColsLab ol cf (indF e S.dom))) S' := by
    refine ⟨⟨gv, encFun (indF e S.dom), xv, yv, _, _, hg, rfl, hx, hy, hHV,
      ⟨_, ⟨_, _, hrowP, ⟨_, hcolsP, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hsv.colors, hsv.fits, ?_⟩
    exact hsv.small.of_rho_le rfl hIOK (colChildState_rho Ic) fun R hR => by
      simp only [hS', colChildState, Option.mem_def, Option.some.injEq] at hR
      subst hR
      exact hqN
  have hgS' := colChildState_good hgood0 htr hsN hrow Ic
  have hcall := ih .cont S' hgS' (colChildState_mlt htr hsN hrow Ic) k e c hc _ hcan
  -- the program computes the child value
  set X := colBrX S.N with hX
  have hP1 : 1 ≤ S.N + 2 := by omega
  have hp36 : (S.N + 2) ^ 3 ≤ (S.N + 2) ^ 6 := Nat.pow_le_pow_right hP1 (by omega)
  have hp16 : S.N + 2 ≤ (S.N + 2) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hXge : (S.N + 2) ^ 6 ≤ X := colBrX_ge S.N
  have hNX : S.N + 2 ≤ X := by omega
  have hsvE' : sv = colSV k gv (indF e S.dom) xv yv (colHV (fun j : Fin S.hier.length => labs j)
      (fun j : Fin S.hier.length => S.hier[j].ratio) (fun j : Fin S.hier.length => S.hier[j].cap)
      (fun j : Fin S.hier.length => S.hier[j].origin)) rv (boolVal S.floor) S.h S.N := by
    rw [hsvE, hhv]; rfl
  have hsvX : sv.wt ≤ X := by
    have := hsv.wt_le_poly
    rw [hX]; unfold colBrX
    have : 10 ^ 4 * (S.N + 2) ^ 6 ≤ 10 ^ 6 * (S.N + 2) ^ 6 :=
      Nat.mul_le_mul_right _ (by norm_num)
    omega
  have hB : ColLevB (X := X) labs (fun j : Fin S.hier.length => S.hier[j].ratio)
      (fun j : Fin S.hier.length => S.hier[j].cap) (fun j : Fin S.hier.length => S.hier[j].origin)
      ol (rowLab e L.con.blocks) (indF e S.dom) := by
    refine ⟨?_, hmk, ?_, fun j i => (hlabk j i).le, fun c => ((holm c).trans_le hmk).le,
      fun i => (colRowLab_le e _ i).trans (by omega), indF_le_one e S.dom, ?_, fun j => ?_⟩
    · have := Nat.pow_le_pow_left (show k + 2 ≤ S.N + 2 by omega) 3
      omega
    · have := hsmall.1
      omega
    · have h1 : (colHV (fun j : Fin S.hier.length => labs j)
          (fun j : Fin S.hier.length => S.hier[j].ratio) (fun j : Fin S.hier.length => S.hier[j].cap)
          (fun j : Fin S.hier.length => S.hier[j].origin)).wt < sv.wt := by
        rw [hsvE']; exact wt_le_wt_list (by simp)
      omega
    · exact le_trans (hsmall.2.1 _ (List.getElem_mem j.2)).2.1 (by omega)
  have hR0 : (colRowsR e S E)[0]? = some ((List.finRange m).map fun c => (r0 c : ℕ)) := by
    simp [colRowsR, hr0, hq0]
  have hRB : ∀ r ∈ colRowsR e S E, (∀ x ∈ r, x ≤ X) ∧ r.length ≤ X := by
    intro r hr'
    simp only [colRowsR, List.mem_map, List.mem_finRange, true_and] at hr'
    obtain ⟨j, rfl⟩ := hr'
    refine ⟨fun x hx => ?_, by simp; omega⟩
    simp only [List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨β, rfl⟩ := hx
    have := (e (E (β, j))).2
    omega
  have hrlR : ∀ i, indF e S.dom i ≠ 0 → rowLab e L.con.blocks i < (colRowsR e S E).length := by
    intro i hi
    rw [hrlD i ((colIndF_ne_zero e S.dom i).1 hi)]
    simp [colRowsR]
  have hcfv : ∀ i, (cf i : ℕ) = colInvv (colRowsR e S E) (indF e S.dom) (rowLab e L.con.blocks) i :=
    colCf_inv e S E h0 label hP.label_e _ hrlD
  have hW := colBrIn_wt_le hsv L.con.blocks E hq0 hlN (σN := σN)
  rw [hsvE'] at hW
  have hhX : S.h ≤ X := by have := S.h_le; omega
  have hdet := colChild_det (P := Pg) (b := b) (fc := F.cont) hA h0 hB J hJ hol hR0 hRB hrlR hcfv
    hW (by omega) hhX
  rw [← hsvE'] at hdet
  refine FunAll.intro hA.main (EvalAll.call_funAll hdet fun v' ca h => ?_)
  obtain ⟨rfl, hca⟩ := h
  refine hcall.mono fun u cs ⟨A, L', r, hL, hAns, hcs⟩ => ?_
  have hL' : L' = none := hL
  subst hL'
  obtain ⟨hh1, -⟩ := column_step_counter P₀_terminating.third_lt_α S htr hsN L.toGiantLabels hrow Ic
  refine ⟨A, Run.rowColumns (S' := S') hth htr L hrow Ic ⟨rfl, rfl, rfl, rfl⟩ rfl hh1 rfl rfl rfl r,
    rfl, hAns, ?_⟩
  have hch : I.childCost (Run.rowColumns (S' := S') hth htr L hrow Ic ⟨rfl, rfl, rfl, rfl⟩ rfl hh1
      rfl rfl rfl r) = r.total I.work := by
    simp only [childCost, Run.children, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, charge, reduceCtorEq, if_false]
  rw [hch]
  simp only [excess, reduceCtorEq, if_false, add_zero] at hcs
  have hu : u.wt ≤ 1000 * (S.N + 2) ^ 6 := hAns.wt_le.trans (ansW_le_N hkN)
  have hCo : orbitK * ((σN.length + 1) * (m + 1)) ^ 5 ≤ orbitK * (4 * (S.N + 2) ^ 3) ^ 5 := by
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 5)
    have h1 : (k + L.q) ^ 2 ≤ (2 * S.N) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 * S.N) ^ 2 = 4 * S.N ^ 2 := by ring
    have h3 : σN.length + 1 ≤ 4 * (S.N + 2) ^ 2 := by
      have : (S.N + 2) ^ 2 = S.N ^ 2 + 4 * S.N + 4 := by ring
      omega
    calc (σN.length + 1) * (m + 1) ≤ (4 * (S.N + 2) ^ 2) * (S.N + 2) :=
          Nat.mul_le_mul h3 (by omega)
      _ = 4 * (S.N + 2) ^ 3 := by ring
  have htot : ca + u.wt + 1 ≤ colBrPoly S.N := by
    unfold colBrPoly
    rw [← hX]
    generalize orbitK * ((σN.length + 1) * (m + 1)) ^ 5 = a at hca hCo
    generalize orbitK * (4 * (S.N + 2) ^ 3) ^ 5 = a' at hCo ⊢
    generalize 10 ^ 34 * (X + 1) ^ 6 = x at hca ⊢
    omega
  push_cast
  have : ((ca + u.wt + 1 : ℕ) : ℝ) ≤ (colBrPoly S.N : ℝ) := by exact_mod_cast htot
  push_cast at this
  linarith

end Iface

end GI.Impl
