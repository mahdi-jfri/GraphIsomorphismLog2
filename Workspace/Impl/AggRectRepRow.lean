import Workspace.Impl.AggRectRepPair

/-!
# The row numbers of a retained row record

Lemma A.30 couples the column giant to `q` chosen rows. The state keeps the row partition
(`RowRecord.rows`) but not a numbering of the rows; the carrier invariant (`CarrierOK`) only
says that *some* numbering `row' : Ω → [m]` with a row action `ρ'` is a carrier
(`CarrierSpec`). The program numbers the rows itself: the *key* of a position is the least
position of its row in the domain (`rcRKey`), and the number of the row is the number of keys
below it (`rcRRow`).

`rcR_carrierSpec`: these row numbers are a carrier as well, with the row action
`ρ(g) = σ ρ'(g) σ⁻¹` for the renumbering `σ` of the rows (`row = σ ∘ row'` on the domain). So
the data of Lemma A.30 can be built from them (`CarrierData.ofSpec`), and the program can read
off `ρ(g)` on the rows: `ρ(g)(row v) = row(g v)` (`CarrierSpec.row_equivariant`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm

variable {Ω : Type} {k : ℕ} (e : Ω ≃ Fin k) (D : Set Ω) (rows : Setoid Ω)

open Classical in
/-- The positions of the domain in the row of `v`. -/
noncomputable def rcRKeySet (v : Ω) : Finset (Fin k) :=
  Finset.univ.filter fun j => e.symm j ∈ D ∧ rows.r (e.symm j) v

open Classical in
/-- **The key of a position**: the least position of its row in the domain. -/
noncomputable def rcRKey (v : Ω) : Fin k :=
  if h : (rcRKeySet e D rows v).Nonempty then (rcRKeySet e D rows v).min' h else e v

open Classical in
/-- The keys of the rows met by the domain. -/
noncomputable def rcRKeys : Finset (Fin k) :=
  (Finset.univ.filter fun j => e.symm j ∈ D).image fun j => rcRKey e D rows (e.symm j)

open Classical in
/-- The number of keys below `t`. -/
noncomputable def rcRRank (t : Fin k) : ℕ := ((rcRKeys e D rows).filter (· < t)).card

variable {e D rows}

theorem rcR_mem_keySet {v : Ω} {j : Fin k} :
    j ∈ rcRKeySet e D rows v ↔ e.symm j ∈ D ∧ rows.r (e.symm j) v := by
  classical
  simp [rcRKeySet]

theorem rcR_keySet_ne {v : Ω} (hv : v ∈ D) : (rcRKeySet e D rows v).Nonempty :=
  ⟨e v, rcR_mem_keySet.2 ⟨by simpa using hv, by simp⟩⟩

theorem rcR_key_mem {v : Ω} (hv : v ∈ D) : rcRKey e D rows v ∈ rcRKeySet e D rows v := by
  unfold rcRKey
  rw [dif_pos (rcR_keySet_ne hv)]
  exact Finset.min'_mem _ _

theorem rcR_key_rel {v : Ω} (hv : v ∈ D) :
    e.symm (rcRKey e D rows v) ∈ D ∧ rows.r (e.symm (rcRKey e D rows v)) v :=
  rcR_mem_keySet.1 (rcR_key_mem hv)

/-- **Two positions of the domain have the same key exactly when they share a row.** -/
theorem rcR_key_eq_iff {v w : Ω} (hv : v ∈ D) (hw : w ∈ D) :
    rcRKey e D rows v = rcRKey e D rows w ↔ rows.r v w := by
  constructor
  · intro h
    have h1 := (rcR_key_rel (rows := rows) (e := e) hv).2
    have h2 := (rcR_key_rel (rows := rows) (e := e) hw).2
    rw [h] at h1
    exact rows.trans (rows.symm h1) h2
  · intro h
    have hs : rcRKeySet e D rows v = rcRKeySet e D rows w := by
      ext j
      rw [rcR_mem_keySet, rcR_mem_keySet]
      exact and_congr_right fun _ => ⟨fun h' => rows.trans h' h, fun h' => rows.trans h' (rows.symm h)⟩
    unfold rcRKey
    rw [dif_pos (rcR_keySet_ne hv), dif_pos (rcR_keySet_ne hw)]
    congr 1

theorem rcR_key_mem_keys {v : Ω} (hv : v ∈ D) : rcRKey e D rows v ∈ rcRKeys e D rows := by
  classical
  simp only [rcRKeys, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e v, by simpa using hv, by simp⟩

theorem rcR_mem_keys {t : Fin k} :
    t ∈ rcRKeys e D rows ↔ ∃ v ∈ D, rcRKey e D rows v = t := by
  classical
  simp only [rcRKeys, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨_, hj, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨e v, by simpa using hv, by simp⟩

/-- A key is the key of its own position. -/
theorem rcR_key_key {v : Ω} (hv : v ∈ D) :
    rcRKey e D rows (e.symm (rcRKey e D rows v)) = rcRKey e D rows v :=
  (rcR_key_eq_iff (rcR_key_rel hv).1 hv).2 (rcR_key_rel hv).2

/-! ### Ranks -/

theorem rcR_rank_lt {t : Fin k} (ht : t ∈ rcRKeys e D rows) :
    rcRRank e D rows t < (rcRKeys e D rows).card := by
  classical
  unfold rcRRank
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h ht
  simp at this

theorem rcR_rank_strict {t t' : Fin k} (ht : t ∈ rcRKeys e D rows) (h : t < t') :
    rcRRank e D rows t < rcRRank e D rows t' := by
  classical
  unfold rcRRank
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
  · have := hsub (Finset.mem_filter.2 ⟨ht, h⟩)
    simp at this

theorem rcR_rank_inj {t t' : Fin k} (ht : t ∈ rcRKeys e D rows) (ht' : t' ∈ rcRKeys e D rows)
    (h : rcRRank e D rows t = rcRRank e D rows t') : t = t' := by
  rcases lt_trichotomy t t' with hl | rfl | hl
  · exact absurd h (rcR_rank_strict ht hl).ne
  · rfl
  · exact absurd h (rcR_rank_strict ht' hl).ne'

theorem rcR_rank_onto {i : ℕ} (hi : i < (rcRKeys e D rows).card) :
    ∃ t ∈ rcRKeys e D rows, rcRRank e D rows t = i := by
  classical
  obtain ⟨t, ht, he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := rcRKeys e D rows)
    (t := Finset.range (rcRKeys e D rows).card) (fun t _ => rcRRank e D rows t)
    (fun t ht => Finset.mem_range.2 (rcR_rank_lt ht))
    (fun t t' ht ht' h => rcR_rank_inj ht ht' h) (by simp) i (Finset.mem_range.2 hi)
  exact ⟨t, ht, he.symm⟩

/-! ### The row numbers -/

variable {G : Subgroup (Perm Ω)} {m : ℕ} {c : Setoid Ω} {row' : Ω → Fin m}
  {ρ' : G →* alternatingGroup (Fin m)}

/-- The number of rows met by the domain is `m`. -/
theorem rcR_keys_card (hs : CarrierSpec G D m rows c row' ρ') : (rcRKeys e D rows).card = m := by
  classical
  have hcard : (rcRKeys e D rows).card = (Finset.univ : Finset (Fin m)).card := by
    refine Finset.card_bij (fun t _ => row' (e.symm t)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro t ht t' ht' h
      obtain ⟨v, hv, rfl⟩ := rcR_mem_keys.1 ht
      obtain ⟨w, hw, rfl⟩ := rcR_mem_keys.1 ht'
      have h1 := (rcR_key_rel (rows := rows) (e := e) hv).1
      have h2 := (rcR_key_rel (rows := rows) (e := e) hw).1
      have hr := (hs.row_iff _ h1 _ h2).2 h
      rw [← rcR_key_key hv, ← rcR_key_key hw]
      exact (rcR_key_eq_iff h1 h2).2 hr
    · intro i _
      obtain ⟨v, hv, rfl⟩ := hs.row_onto i
      refine ⟨_, rcR_key_mem_keys hv, ?_⟩
      have h1 := rcR_key_rel (rows := rows) (e := e) hv
      exact (hs.row_iff _ h1.1 _ hv).1 h1.2
  simpa using hcard

/-- **The row number of a position**: the number of keys below its key. -/
noncomputable def rcRRow (e : Ω ≃ Fin k) (D : Set Ω) (rows : Setoid Ω) (hm : 0 < m) (v : Ω) : Fin m :=
  if h : rcRRank e D rows (rcRKey e D rows v) < m then ⟨_, h⟩ else ⟨0, hm⟩

variable (hs : CarrierSpec G D m rows c row' ρ')
include hs

theorem rcR_row_val {v : Ω} (hv : v ∈ D) (hm : 0 < m) :
    (rcRRow e D rows hm v : ℕ) = rcRRank e D rows (rcRKey e D rows v) := by
  unfold rcRRow
  rw [dif_pos (by rw [← rcR_keys_card hs]; exact rcR_rank_lt (rcR_key_mem_keys hv))]

theorem rcR_row_iff (hm : 0 < m) {v w : Ω} (hv : v ∈ D) (hw : w ∈ D) :
    rows.r v w ↔ rcRRow e D rows hm v = rcRRow e D rows hm w := by
  rw [← rcR_key_eq_iff (e := e) hv hw]
  constructor
  · intro h
    exact Fin.ext (by rw [rcR_row_val hs hv, rcR_row_val hs hw, h])
  · intro h
    have h' := congrArg Fin.val h
    rw [rcR_row_val hs hv, rcR_row_val hs hw] at h'
    exact rcR_rank_inj (rcR_key_mem_keys hv) (rcR_key_mem_keys hw) h'

theorem rcR_row_onto (hm : 0 < m) (i : Fin m) :
    ∃ v ∈ D, rcRRow e D rows hm v = i := by
  obtain ⟨t, ht, hr⟩ := rcR_rank_onto (e := e) (D := D) (rows := rows)
    (i := i) (by rw [rcR_keys_card hs]; exact i.isLt)
  obtain ⟨v, hv, rfl⟩ := rcR_mem_keys.1 ht
  exact ⟨v, hv, Fin.ext (by rw [rcR_row_val hs hv, hr])⟩

/-! ### The renumbering and the row action -/

/-- The renumbering of the rows: the new number of the row numbered `i` by `row'`. -/
noncomputable def rcRSig (e : Ω ≃ Fin k) (D : Set Ω) (rows : Setoid Ω) (hs : CarrierSpec G D m rows c row' ρ') (hm : 0 < m) (i : Fin m) : Fin m :=
  rcRRow e D rows hm (hs.row_onto i).choose

theorem rcR_row_sig (hm : 0 < m) {v : Ω} (hv : v ∈ D) :
    rcRRow e D rows hm v = rcRSig e D rows hs hm (row' v) := by
  have h := (hs.row_onto (row' v)).choose_spec
  exact (rcR_row_iff hs hm hv h.1).1 ((hs.row_iff _ hv _ h.1).2 h.2.symm)

theorem rcR_sig_bij (hm : 0 < m) : Function.Bijective (rcRSig e D rows hs hm) := by
  refine Finite.injective_iff_bijective.1 fun i j h => ?_
  have hi := (hs.row_onto i).choose_spec
  have hj := (hs.row_onto j).choose_spec
  have h' := (rcR_row_iff hs hm hi.1 hj.1).2 h
  rw [← hi.2, ← hj.2]
  exact (hs.row_iff _ hi.1 _ hj.1).1 h'

/-- The renumbering as a permutation. -/
noncomputable def rcRSigP (e : Ω ≃ Fin k) (hs : CarrierSpec G D m rows c row' ρ') (hm : 0 < m) : Perm (Fin m) :=
  Equiv.ofBijective _ (rcR_sig_bij (e := e) hs hm)

omit hs in
theorem rcR_conj_alt (σ : Perm (Fin m)) {a : Perm (Fin m)} (ha : a ∈ alternatingGroup (Fin m)) :
    σ * a * σ⁻¹ ∈ alternatingGroup (Fin m) := by
  rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, ha.out, mul_one]
  exact Int.units_mul_self _

/-- **The row action for the new numbers**: `ρ(g) = σ ρ'(g) σ⁻¹`. -/
noncomputable def rcRRho (e : Ω ≃ Fin k) (hs : CarrierSpec G D m rows c row' ρ') (hm : 0 < m) :
    G →* alternatingGroup (Fin m) where
  toFun g := ⟨rcRSigP e hs hm * (ρ' g : Perm (Fin m)) * (rcRSigP e hs hm)⁻¹,
    rcR_conj_alt _ (ρ' g).2⟩
  map_one' := by ext i; simp
  map_mul' g h := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group

theorem rcR_rho_val (hm : 0 < m) (g : G) :
    ((rcRRho e hs hm g : alternatingGroup (Fin m)) : Perm (Fin m)) =
      rcRSigP e hs hm * (ρ' g : Perm (Fin m)) * (rcRSigP e hs hm)⁻¹ := rfl

/-- **The new row numbers are a carrier**, for a domain kept by `G`. -/
theorem rcR_carrierSpec (hm : 0 < m) (hD : ∀ g ∈ G, ∀ v ∈ D, g v ∈ D) :
    CarrierSpec G D m rows c (rcRRow e D rows hm) (rcRRho e hs hm) where
  three_le := hs.three_le
  row_iff v hv w hw := rcR_row_iff hs hm hv hw
  row_onto i := rcR_row_onto hs hm i
  row_equivariant g v hv := by
    have hgv : (g : Perm Ω) v ∈ D := hD g g.2 v hv
    rw [rcR_row_sig hs hm hgv, rcR_row_sig hs hm hv, hs.row_equivariant g v hv, rcR_rho_val]
    show rcRSig e D rows hs hm _ = rcRSigP e hs hm ((ρ' g : Perm (Fin m)) ((rcRSigP e hs hm)⁻¹
      (rcRSigP e hs hm (row' v))))
    rw [Perm.inv_apply_self]
    rfl
  cols_inv := hs.cols_inv
  two_cols := hs.two_cols
  indep a := by
    obtain ⟨g, hg, hf⟩ := hs.indep ⟨(rcRSigP e hs hm)⁻¹ * a * rcRSigP e hs hm, by
      have := rcR_conj_alt (rcRSigP e hs hm)⁻¹ a.2
      rwa [inv_inv] at this⟩
    refine ⟨g, Subtype.ext ?_, hf⟩
    rw [rcR_rho_val, hg]
    simp only
    group
  cells v hv w hw hr hc := by
    obtain ⟨g, hg, hf, hgv⟩ := hs.cells v hv w hw (by
      rw [rcR_row_sig hs hm hv, rcR_row_sig hs hm hw] at hr
      exact (rcR_sig_bij hs hm).1 hr) hc
    refine ⟨g, Subtype.ext ?_, hf, hgv⟩
    rw [rcR_rho_val, hg]
    simp

end GI.Impl
