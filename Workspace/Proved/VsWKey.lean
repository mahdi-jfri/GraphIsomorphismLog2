module

public import Workspace.Proved.VsWLinMath
public import Workspace.Proved.VsQMat

@[expose] public section

/-!
# A canonical key for a subspace

To compare subspaces (for example as points of an orbit), we need a key that depends only on
the subspace. We use `vsWKey p d us`: the unit vectors `e_i` sifted through the echelon rows of
`us`. This is the reduced normal form `NF(e_i)`.

Why it is canonical. Each row starts at its pivot: it is `0` before the pivot (`VsWLead`). So the
first nonzero position of any nonzero vector of the span is a pivot (`vsWLead_exists`), and the
set of pivots depends only on the span. The sifted `e_i` is the unique vector of `e_i + U` that is
`0` at all pivots (`vsSpan_eq_zero`). Conversely the key determines `U`, as the vectors `v` with
`∑ v_i NF(e_i) = 0`.

* `vsWKey_eq_iff`: `vsWKey p d us = vsWKey p d ws ↔ vsWSp p d us = vsWSp p d ws`.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-- Each row is `0` before its pivot. -/
def VsWLead (p : ℕ) (rows : List VsRow) : Prop := ∀ r ∈ rows, ∀ i < r.j, vsF p r.x i = 0

theorem vsWNewRow_lead {y : List ℕ × List ℕ} : ∀ i < vsNzIdx y.1,
    vsF p (vsNewRow p y (vsNzIdx y.1)).x i = 0 := by
  intro i hi
  have hy : y.1.getD i 0 = 0 := by
    have hlt : i < y.1.length := lt_of_lt_of_le hi (vsNzIdx_le _)
    have := List.not_of_lt_findIdx hi
    rw [List.getD_eq_getElem _ _ hlt]
    simpa using this
  have hlt : i < y.1.length := lt_of_lt_of_le hi (vsNzIdx_le _)
  rw [vsF_apply, vsNewRow, vsLin_getD _ _ _ _ _ hlt, hy]
  simp

theorem vsWFold_lead :
    ∀ (L : List (List ℕ × List ℕ)) (acc : List VsRow × List (List ℕ)),
    VsWLead p acc.1 → VsWLead p (L.foldl (vsAllStep p) acc).1
  | [], _, h => h
  | xt :: L, acc, h => by
    refine vsWFold_lead L _ ?_
    unfold vsAllStep
    split_ifs
    · intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h r hr
      · exact vsWNewRow_lead
    · exact h

theorem vsWRows_lead (us : List (List ℕ)) : VsWLead p (vsWRows p us) :=
  vsWFold_lead _ ([], []) (by simp [VsWLead])

/-- **First nonzero positions are pivots.** -/
theorem vsWLead_exists {rows : List VsRow} (he : VsEch p rows) (hl : VsWLead p rows)
    {v : ℕ → ZMod p} (hv : v ∈ vsSpan p rows) (h0 : v ≠ 0) :
    ∃ r ∈ rows, v r.j ≠ 0 ∧ ∀ i < r.j, v i = 0 := by
  induction rows generalizing v with
  | nil => rw [vsSpan_nil, Submodule.mem_bot] at hv; exact absurd hv h0
  | cons r rs ih =>
    obtain ⟨h1, hz, hrs⟩ := he
    have hl' : VsWLead p rs := fun r' hr' => hl r' (by simp [hr'])
    have hlr := hl r (by simp)
    rw [vsSpan_cons, Submodule.mem_span_insert] at hv
    obtain ⟨a, w, hw, rfl⟩ := hv
    have hw' : w ∈ vsSpan p rs := hw
    have hwj : w r.j = 0 := vsSpan_apply_zero hz hw'
    by_cases ha : a = 0
    · subst ha
      simp only [zero_smul, zero_add] at h0 ⊢
      obtain ⟨r', hr', h2, h3⟩ := ih hrs hl' hw' h0
      exact ⟨r', by simp [hr'], h2, h3⟩
    by_cases hw0 : w = 0
    · subst hw0
      refine ⟨r, by simp, ?_, fun i hi => ?_⟩
      · simp [h1, ha]
      · simp [hlr i hi]
    obtain ⟨r', hr', h2, h3⟩ := ih hrs hl' hw' hw0
    rcases Nat.lt_trichotomy r.j r'.j with hlt | heq | hgt
    · refine ⟨r, by simp, ?_, fun i hi => ?_⟩
      · simp [h1, hwj, ha]
      · simp [hlr i hi, h3 i (hi.trans hlt)]
    · exact absurd (heq ▸ hwj) h2
    · refine ⟨r', by simp [hr'], ?_, fun i hi => ?_⟩
      · simp [hlr _ hgt, h2]
      · simp [hlr i (hi.trans hgt), h3 i hi]

theorem vsWEch_one {rows : List VsRow} (he : VsEch p rows) : ∀ r ∈ rows, vsF p r.x r.j = 1 := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | h
    · exact he.1
    · exact ih he.2.2 r' h

/-- Two echelon row lists with the same span have the same pivots. -/
theorem vsWPivots (hp : p.Prime) {R1 R2 : List VsRow} (he1 : VsEch p R1) (hl1 : VsWLead p R1)
    (he2 : VsEch p R2) (hl2 : VsWLead p R2) (hs : vsSpan p R1 = vsSpan p R2) :
    ∀ r ∈ R1, ∃ r2 ∈ R2, r2.j = r.j := by
  haveI := Fact.mk hp
  intro r hr
  have h1 := vsWEch_one he1 r hr
  have hm : vsF p r.x ∈ vsSpan p R2 := hs ▸ vsF_mem_vsSpan p hr
  have h0 : vsF p r.x ≠ 0 := fun h => by
    have := congrFun h r.j; rw [h1] at this; exact one_ne_zero this
  obtain ⟨r2, hr2, h2, h3⟩ := vsWLead_exists he2 hl2 hm h0
  refine ⟨r2, hr2, ?_⟩
  rcases Nat.lt_trichotomy r2.j r.j with hlt | heq | hgt
  · exact absurd (hl1 r hr _ hlt) h2
  · exact heq
  · have := h3 _ hgt; rw [h1] at this; exact absurd this one_ne_zero

/-- **Normal forms agree.** Sifting through two echelon row lists with the same span gives the
same vector. -/
theorem vsWNF_eq (hp : p.Prime) {R1 R2 : List VsRow} (he1 : VsEch p R1) (hl1 : VsWLead p R1)
    (he2 : VsEch p R2) (hl2 : VsWLead p R2) (hs : vsSpan p R1 = vsSpan p R2)
    {xt : List ℕ × List ℕ} (hb : VsBelow p xt) (hs1 : VsShort xt R1) (hs2 : VsShort xt R2) :
    vsF p (vsSift p R1 xt).1 = vsF p (vsSift p R2 xt).1 := by
  have d1 := vsSift_sub_mem hp.pos R1 hb hs1
  have d2 := vsSift_sub_mem hp.pos R2 hb hs2
  rw [← hs] at d2
  have hd := Submodule.sub_mem _ d2 d1
  rw [sub_sub_sub_cancel_left] at hd
  have z := vsSpan_eq_zero he1 hd fun r hr => by
    obtain ⟨r2, hr2, hj⟩ := vsWPivots hp he1 hl1 he2 hl2 hs r hr
    rw [Pi.sub_apply, vsSift_zero_at hp.pos he1 hb hs1 r hr, ← hj,
      vsSift_zero_at hp.pos he2 hb hs2 r2 hr2, sub_zero]
  exact sub_eq_zero.mp z

theorem vsWUnit_below (hp : 1 < p) (d i : ℕ) : VsBelow p (vsUnit d i, ([] : List ℕ)) :=
  fun y hy => lt_of_le_of_lt (vsUnit_le_one d i y hy) hp

theorem vsWRows_short (hp : 0 < p) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) (i : ℕ) :
    VsShort (vsUnit d i, ([] : List ℕ)) (vsWRows p us) := by
  intro r hr
  have := (vsWAcc_shape hp (vsWPairs_ok h)).rows r hr
  simp only [vsUnit_length, List.length_nil]
  exact ⟨this.2.2.1.le, this.2.2.2.le⟩

theorem vsWKey_fit (hp : 1 < p) {d : ℕ} (us : List (List ℕ)) : VsWFit p d (vsWKey p d us) := by
  intro x hx
  simp only [vsWKey, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  have := vsSift_fits (by omega) (vsWRows p us) (N := d + p) (xt := (vsUnit d i, []))
    ⟨vsWUnit_below hp d i, by simp, by rw [vsUnit_length]; omega, by simp⟩
  exact ⟨this.hx, by rw [(vsSift_length _ _ _).1, vsUnit_length]⟩

/-- Equal spans give equal keys. -/
theorem vsWKey_of_eq (hp : p.Prime) {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us)
    (hw : VsWFit p d ws) (h : vsWSp p d us = vsWSp p d ws) : vsWKey p d us = vsWKey p d ws := by
  haveI := Fact.mk hp
  rw [vsWSp_eq_iff (fun u hu' => (hu u hu').2.le) (fun w hw' => (hw w hw').2.le)] at h
  obtain ⟨he1, -, hs1⟩ := vsWRows_inv hp hu
  obtain ⟨he2, -, hs2⟩ := vsWRows_inv hp hw
  have hs : vsSpan p (vsWRows p us) = vsSpan p (vsWRows p ws) := by rw [hs1, hs2, h]
  have hk1 := vsWKey_fit (d := d) hp.one_lt us
  have hk2 := vsWKey_fit (d := d) hp.one_lt ws
  refine List.ext_getElem (by simp [vsWKey]) fun i h1 h2 => ?_
  have f1 := hk1 _ (List.getElem_mem h1)
  have f2 := hk2 _ (List.getElem_mem h2)
  rw [vsQVec_of f1.2 f1.1, vsQVec_of f2.2 f2.1]
  congr 1
  funext j
  simp only [vsWKey, List.getElem_map, List.getElem_range]
  rw [vsWNF_eq hp he1 (vsWRows_lead us) he2 (vsWRows_lead ws) hs (vsWUnit_below hp.one_lt d i)
    (vsWRows_short hp.pos hu i) (vsWRows_short hp.pos hw i)]

/-- **The key determines the span.** A vector `v` supported below `d` lies in the span exactly
when `∑ v_i NF(e_i) = 0`. -/
theorem vsWKey_mem (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (hu : VsWFit p d us)
    {v : ℕ → ZMod p} (hv : v ∈ vsWSupp p d) :
    v ∈ vsWSpN p us ↔
      ∑ i ∈ Finset.range d, v i • vsF p ((vsWKey p d us).getD i []) = 0 := by
  obtain ⟨he, -, hs⟩ := vsWRows_inv hp hu
  set Φ := ∑ i ∈ Finset.range d, v i • vsF p ((vsWKey p d us).getD i [])
  have hK : ∀ i < d, (vsWKey p d us).getD i [] = (vsSift p (vsWRows p us) (vsUnit d i, [])).1 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa [vsWKey] using hi)]
    simp [vsWKey]
  have hv' : v = ∑ i ∈ Finset.range d, v i • vsF p (vsUnit d i) := by
    funext j
    rw [Finset.sum_apply]
    by_cases hj : j < d
    · rw [Finset.sum_eq_single j]
      · simp [vsF_vsUnit hj]
      · intro i hi hij
        simp [vsF_vsUnit (Finset.mem_range.mp hi), Pi.single_apply, Ne.symm hij]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [hv j (by omega)]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      have hi' := Finset.mem_range.mp hi
      simp [vsF_vsUnit hi', Pi.single_apply, show j ≠ i by omega]
  have hdiff : v - Φ ∈ vsSpan p (vsWRows p us) := by
    have : v - Φ = ∑ i ∈ Finset.range d, v i • (vsF p (vsUnit d i) -
        vsF p ((vsWKey p d us).getD i [])) := by
      conv_lhs => rw [hv']
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_sub]
    rw [this]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    rw [hK i (Finset.mem_range.mp hi)]
    exact vsSift_sub_mem hp.pos _ (vsWUnit_below hp.one_lt d i) (vsWRows_short hp.pos hu i)
  have hzero : ∀ r ∈ vsWRows p us, Φ r.j = 0 := by
    intro r hr
    simp only [Φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hK i (Finset.mem_range.mp hi), vsSift_zero_at hp.pos he (vsWUnit_below hp.one_lt d i)
      (vsWRows_short hp.pos hu i) r hr, mul_zero]
  rw [← hs]
  constructor
  · intro hm
    have : Φ ∈ vsSpan p (vsWRows p us) := by
      have := Submodule.sub_mem _ hm hdiff
      rwa [sub_sub_cancel] at this
    exact vsSpan_eq_zero he this hzero
  · intro h0
    have := hdiff
    rwa [show Φ = 0 from h0, sub_zero] at this

/-- **The key is canonical.** -/
theorem vsWKey_eq_iff (hp : p.Prime) {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us)
    (hw : VsWFit p d ws) : vsWKey p d us = vsWKey p d ws ↔ vsWSp p d us = vsWSp p d ws := by
  refine ⟨fun hk => ?_, vsWKey_of_eq hp hu hw⟩
  have s1 := vsWSpN_le_supp (p := p) fun u h => (hu u h).2.le
  have s2 := vsWSpN_le_supp (p := p) fun w h => (hw w h).2.le
  rw [vsWSp_eq_iff (fun u h => (hu u h).2.le) (fun w h => (hw w h).2.le)]
  ext v
  constructor
  · intro hm
    have hs := s1 hm
    have h0 := (vsWKey_mem hp hu hs).mp hm
    rw [hk] at h0
    exact (vsWKey_mem hp hw hs).mpr h0
  · intro hm
    have hs := s2 hm
    have h0 := (vsWKey_mem hp hw hs).mp hm
    rw [← hk] at h0
    exact (vsWKey_mem hp hu hs).mpr h0

end GI.Proved
