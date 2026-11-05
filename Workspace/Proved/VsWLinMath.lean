module

public import Workspace.Proved.VsWBasic

@[expose] public section

/-!
# What the linear algebra functions compute

Each function of `Impl/VsWDefs.lean` is described here by a statement about subspaces of
`Fin d → ZMod p`. The proofs go through the L0 facts on `ℕ → ZMod p` and then restrict
(`Proved/VsWBasic.lean`).

* `vsWAcc_shape`: rows and relations of an insertion keep entries below `p` and the lengths of
  the inputs.
* `vsWBas_span`, `vsWBas_indep`, `vsWBas_fit`: an echelon basis.
* `vsWKer_span`, `vsWKer_fit`, `vsWKer_mat`: the relations span the kernel.
* `vsWSolve_none`, `vsWSolve_some`: solving.
* `vsWInter_span`: intersections.
* `vsWImg_span`, `vsWCut_span`: images and the part in a kernel.
* `vsWSubC_matrix`: a stored matrix minus a scalar.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-! ### The shape of an insertion -/

/-- Rows and relations with entries below `p` and the lengths `lx`, `lt` of the inputs. -/
structure VsWShape (p lx lt : ℕ) (acc : List VsRow × List (List ℕ)) : Prop where
  rows : ∀ r ∈ acc.1, (∀ y ∈ r.x, y < p) ∧ (∀ y ∈ r.t, y < p) ∧ r.x.length = lx ∧ r.t.length = lt
  rels : ∀ t ∈ acc.2, (∀ y ∈ t, y < p) ∧ t.length = lt

/-- A pair with entries below `p` in both parts and lengths `lx`, `lt`. -/
def VsWPairOK (p lx lt : ℕ) (xt : List ℕ × List ℕ) : Prop :=
  (∀ y ∈ xt.1, y < p) ∧ (∀ y ∈ xt.2, y < p) ∧ xt.1.length = lx ∧ xt.2.length = lt

theorem vsWAllStep_shape (hp : 0 < p) {lx lt : ℕ} {acc : List VsRow × List (List ℕ)}
    (ha : VsWShape p lx lt acc) {xt : List ℕ × List ℕ} (hx : VsWPairOK p lx lt xt) :
    VsWShape p lx lt (vsAllStep p acc xt) ∧ acc.1 <+: (vsAllStep p acc xt).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hf := vsSift_fits hp acc.1 (N := xt.1.length + xt.2.length + p) (xt := xt)
    ⟨h1, h2, by omega, by omega⟩
  obtain ⟨e1, e2⟩ := vsSift_length p acc.1 xt
  unfold vsAllStep
  split_ifs
  · refine ⟨⟨fun r hr => ?_, ha.rels⟩, List.prefix_append _ _⟩
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact ha.rows r hr
    · refine ⟨vsLin_lt hp _ _, vsLin_lt hp _ _, ?_, ?_⟩
      · simp only [vsNewRow, vsLin_length]; omega
      · simp only [vsNewRow, vsLin_length]; omega
  · refine ⟨⟨ha.rows, fun t ht => ?_⟩, List.prefix_refl _⟩
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ha.rels t ht
    · exact ⟨hf.ht, by omega⟩

theorem vsWFold_shape (hp : 0 < p) {lx lt : ℕ} :
    ∀ (L : List (List ℕ × List ℕ)) (acc : List VsRow × List (List ℕ)),
    (∀ xt ∈ L, VsWPairOK p lx lt xt) → VsWShape p lx lt acc →
    VsWShape p lx lt (L.foldl (vsAllStep p) acc) ∧ acc.1 <+: (L.foldl (vsAllStep p) acc).1
  | [], acc, _, ha => ⟨ha, List.prefix_refl _⟩
  | xt :: L, acc, hL, ha => by
    obtain ⟨s1, p1⟩ := vsWAllStep_shape hp ha (hL xt (List.mem_cons_self ..))
    obtain ⟨s2, p2⟩ := vsWFold_shape hp L _ (fun y hy => hL y (List.mem_cons_of_mem _ hy)) s1
    exact ⟨s2, p1.trans p2⟩

/-- **Shape of an insertion.** -/
theorem vsWAcc_shape (hp : 0 < p) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsWPairOK p lx lt xt) : VsWShape p lx lt (vsInsertAll p L) :=
  (vsWFold_shape hp L ([], []) hL ⟨by simp, by simp⟩).1

/-- Inserting more pairs only appends rows. -/
theorem vsWInsertAll_append (p : ℕ) (L L' : List (List ℕ × List ℕ)) :
    vsInsertAll p (L ++ L') = L'.foldl (vsAllStep p) (vsInsertAll p L) := by
  rw [vsInsertAll, vsInsertAll, List.foldl_append]

theorem vsWInsertAll_prefix (hp : 0 < p) {lx lt : ℕ} {L L' : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsWPairOK p lx lt xt) (hL' : ∀ xt ∈ L', VsWPairOK p lx lt xt) :
    (vsInsertAll p L).1 <+: (vsInsertAll p (L ++ L')).1 := by
  rw [vsWInsertAll_append]
  exact (vsWFold_shape hp L' _ hL' (vsWAcc_shape hp hL)).2

theorem VsWPairOK.below {lx lt : ℕ} {xt : List ℕ × List ℕ} (h : VsWPairOK p lx lt xt) :
    VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt := ⟨h.1, h.2.2.1, h.2.2.2⟩

/-! ### Echelon bases -/

theorem vsWPairs_ok {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    ∀ xt ∈ vsWPairs us, VsWPairOK p d 0 xt := by
  intro xt hxt
  simp only [vsWPairs, List.mem_map] at hxt
  obtain ⟨u, hu, rfl⟩ := hxt
  exact ⟨(h u hu).1, by simp, (h u hu).2, rfl⟩

theorem vsWBas_fit (hp : 0 < p) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    VsWFit p d (vsWBas p us) := by
  intro x hx
  simp only [vsWBas, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have := (vsWAcc_shape hp (vsWPairs_ok h)).rows r hr
  exact ⟨this.1, this.2.2.1⟩

theorem vsWBas_spanN (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    vsWSpN p (vsWBas p us) = vsWSpN p us := by
  rw [vsWBas, ← vsSpan_eq_vsWSpN]
  exact (vsWRows_inv hp h).2.2

/-- **The basis spans.** -/
theorem vsWBas_span (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    vsWSp p d (vsWBas p us) = vsWSp p d us := by
  rw [vsWSp_eq_map, vsWSp_eq_map, vsWBas_spanN hp h]

/-- Combinations of the vectors of a list whose vectors have length at most `d`, as a sum over
`range`, are supported below `d`. -/
theorem vsWSum_supp {d : ℕ} {xs : List (List ℕ)} (hx : ∀ x ∈ xs, x.length ≤ d) (g : ℕ → ZMod p) :
    ∑ i ∈ Finset.range xs.length, g i • vsF p (xs.getD i []) ∈ vsWSupp p d :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (vsF_mem_vsWSupp (by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
    exact hx _ (List.getElem_mem _)))

/-- **The basis is independent.** -/
theorem vsWBas_indep (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    LinearIndependent (ZMod p) fun i : Fin (vsWBas p us).length => vsWV p d (vsWBas p us)[i] := by
  obtain ⟨he, hl, -⟩ := vsWRows_inv hp h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set rows := vsWRows p us
  have hlen : (vsWBas p us).length = rows.length := by simp [vsWBas, rows]
  let g' : ℕ → ZMod p := fun i => if hi : i < (vsWBas p us).length then g ⟨i, hi⟩ else 0
  have hsum : ∑ i ∈ Finset.range rows.length, g' i • vsF p (rows.getD i ⟨0, [], []⟩).x = 0 := by
    have hs : ∑ i ∈ Finset.range rows.length, g' i • vsF p (rows.getD i ⟨0, [], []⟩).x ∈
        vsWSupp p d := by
      have := vsWSum_supp (d := d) (xs := vsWBas p us) (fun x hx => ((vsWBas_fit hp.pos h) x hx).2.le) g'
      convert this using 2 with i hi
      · rw [hlen]
      · simp only [vsWBas, List.getD_eq_getElem?_getD, List.getElem?_map, rows]
        cases (vsWRows p us)[i]? <;> rfl
    refine vsWR_eq_zero hs ?_
    rw [map_sum, ← hg, ← Fin.sum_univ_eq_sum_range (fun i => vsWR p d (g' i • vsF p
      (rows.getD i ⟨0, [], []⟩).x))]
    refine Fintype.sum_equiv (finCongr hlen.symm) _ _ fun i => ?_
    simp only [map_smul, g', finCongr_apply, Fin.coe_cast, i.2, hlen, dite_true]
    congr 1
    funext j
    simp [vsWBas, List.getD_eq_getElem _ _ i.2, rows, Fin.cast]
  intro i
  have := vsWEch_indep he hsum i (hlen ▸ i.2)
  simpa [g', i.2] using this

/-! ### Kernels -/

theorem vsWUnitPairs_ok {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) (hp : 1 < p) :
    ∀ xt ∈ vsUnitPairs us.length us, VsWPairOK p d us.length xt := by
  intro xt hxt
  obtain ⟨h1, h2, h3⟩ := vsUnitPairs_fit h xt hxt
  refine ⟨h1, ?_, h2, h3⟩
  simp only [vsUnitPairs, List.mem_map, List.mem_range] at hxt
  obtain ⟨i, hi, rfl⟩ := hxt
  exact fun y hy => lt_of_le_of_lt (vsUnit_le_one _ _ y hy) hp

theorem vsWKer_fit (hp : 1 < p) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    VsWFit p us.length (vsWKer p us) :=
  fun t ht => (vsWAcc_shape (by omega) (vsWUnitPairs_ok h hp)).rels t ht

/-- **The relations span the kernel** of `a ↦ ∑ a_i u_i`. -/
theorem vsWKer_span (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    vsWSp p us.length (vsWKer p us) = LinearMap.ker (vsWComb p d us) := by
  have hfit := vsWKer_fit hp.one_lt h
  have hsupp : vsWSpN p (vsWKer p us) ≤ vsWSupp p us.length :=
    vsWSpN_le_supp fun t ht => (hfit t ht).2.le
  have hker := fun a ha => vsUnitPairs_ker hp h (a := a) ha
  have hspan : Submodule.span (ZMod p) {w | w ∈ (vsWKer p us).map (vsF p)} = vsWSpN p (vsWKer p us) :=
    (vsWSpN_eq_span_list _).symm
  have hcomb : ∀ a, a ∈ vsWSupp p us.length →
      (vsComb p us a = 0 ↔ vsWComb p d us (vsWR p us.length a) = 0) := by
    intro a ha
    rw [← vsWR_vsComb]
    refine ⟨fun h0 => by rw [h0, map_zero], fun h0 => vsWR_eq_zero ?_ h0⟩
    have := vsWSum_supp (d := d) (xs := us) (fun u hu => (h u hu).2.le) a
    exact this
  rw [vsWSp_eq_map]
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haS := hsupp ha
    rw [LinearMap.mem_ker, ← hcomb a haS]
    refine (hker a haS).mpr ?_
    rw [← hspan] at ha; exact ha
  · intro hv
    rw [LinearMap.mem_ker] at hv
    refine ⟨vsWE p us.length v, ?_, vsWR_vsWE _ v⟩
    have hE := vsWE_mem (p := p) us.length v
    have := (hker _ hE).mp ((hcomb _ hE).mpr (by rw [vsWR_vsWE]; exact hv))
    rw [← hspan]; exact this

/-- **Kernel of a stored matrix.** The relations among its rows span the kernel. -/
theorem vsWKer_mat (hp : p.Prime) {d : ℕ} {A : List (List ℕ)} (h : VsWFit p d A)
    (hA : A.length = d) : vsWSp p d (vsWKer p A) = LinearMap.ker (vsWLin p d A) := by
  subst hA
  rw [vsWKer_span hp h]
  ext v
  simp only [LinearMap.mem_ker, vsWLin_apply rfl]
  rfl

/-! ### Solving -/

theorem vsWZ_vsF (m : ℕ) : vsF p (vsWZ m) = 0 := by
  funext j; simp [vsF, vsWZ, List.getD_eq_getElem?_getD]

theorem vsWNeg_vsF (hp : 0 < p) (t : List ℕ) : vsF p (vsWNeg p t) = -vsF p t := by
  rw [vsWNeg, vsF_vsLin _ _ _ le_rfl, Nat.cast_sub (by omega)]
  simp

theorem vsWNeg_lt (hp : 0 < p) (t : List ℕ) : ∀ y ∈ vsWNeg p t, y < p := vsLin_lt hp _ _

theorem vsWNeg_length (p : ℕ) (t : List ℕ) : (vsWNeg p t).length = t.length := vsLin_length ..

theorem vsWUnitPairs_main (us : List (List ℕ)) :
    (vsUnitPairs us.length us).map (fun xt => vsF p xt.1) = us.map (vsF p) := by
  simp only [vsUnitPairs, List.map_map]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

theorem vsWUnitRows_span (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    vsSpan p (vsInsertAll p (vsUnitPairs us.length us)).1 = vsWSpN p us := by
  rw [vsInsertAll_span hp (vsUnitPairs_fit h), vsWUnitPairs_main, vsWSpN_eq_span_list]

/-- **Solving: none.** -/
theorem vsWSolve_none (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us)
    {u : List ℕ} (hu : ∀ y ∈ u, y < p) (hul : u.length = d) :
    vsWSolve p us u = none ↔ vsWV p d u ∉ vsWSp p d us := by
  have hs := vsSolve hp (vsUnitPairs_fit h) hu hul (z := vsWZ us.length) (by simp [vsWZ])
    (vsWZ_vsF _)
  have hb : ∀ y ∈ (vsWSolveSift p us u).1, y < p :=
    (vsSift_fits hp.pos _ (N := u.length + us.length + p) ⟨hu, fun y hy => by
      have := hp.pos; simp [vsWZ] at hy; omega, by simp; omega, by simp [vsWZ]; omega⟩).hx
  have hiff : vsWV p d u ∈ vsWSp p d us ↔ vsF p u ∈ vsWSpN p us := by
    rw [vsWSp_eq_map]
    constructor
    · rintro ⟨f, hf, he⟩
      rwa [← vsWR_injOn ((vsWSpN_le_supp fun w hw => (h w hw).2.le) hf)
        (vsF_mem_vsWSupp hul.le) he]
    · intro hm; exact ⟨_, hm, rfl⟩
  rw [hiff, ← vsWUnitRows_span hp h, ← hs.1]
  unfold vsWSolve
  by_cases h1 : vsNzIdx (vsWSolveSift p us u).1 < (vsWSolveSift p us u).1.length
  · rw [if_pos h1]; simp only [true_iff]; exact (vsNzIdx_lt_iff hb).mp h1
  · rw [if_neg h1]; simp only [reduceCtorEq, false_iff, not_not]
    by_contra hne; exact h1 ((vsNzIdx_lt_iff hb).mpr hne)

/-- **Solving: the coefficients.** -/
theorem vsWSolve_some (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us)
    {u : List ℕ} (hu : ∀ y ∈ u, y < p) (hul : u.length = d) {a : List ℕ}
    (ha : vsWSolve p us u = some a) :
    vsWComb p d us (vsWV p us.length a) = vsWV p d u ∧ VsWFit p us.length [a] := by
  have hb : ∀ y ∈ (vsWSolveSift p us u).1, y < p :=
    (vsSift_fits hp.pos _ (N := u.length + us.length + p) ⟨hu, fun y hy => by
      have := hp.pos; simp [vsWZ] at hy; omega, by simp; omega, by simp [vsWZ]; omega⟩).hx
  unfold vsWSolve at ha
  split_ifs at ha with h1
  cases ha
  have h0 : vsF p (vsWSolveSift p us u).1 = 0 := by
    by_contra hne; exact h1 ((vsNzIdx_lt_iff hb).mpr hne)
  have := vsUnitPairs_solve hp h hu hul (z := vsWZ us.length) (by simp [vsWZ]) (vsWZ_vsF _) h0
  refine ⟨?_, ?_⟩
  · rw [show vsWV p us.length (vsWNeg p (vsWSolveSift p us u).2) =
        vsWR p us.length (-vsF p (vsSift p (vsInsertAll p (vsUnitPairs us.length us)).1
          (u, vsWZ us.length)).2) by rw [vsWV, vsWNeg_vsF hp.pos]; rfl,
      ← vsWR_vsComb, ← this]
    rfl
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    refine ⟨vsWNeg_lt hp.pos _, ?_⟩
    rw [vsWNeg_length, vsWSolveSift, (vsSift_length _ _ _).2]
    simp [vsWZ]

/-! ### Intersections -/

theorem vsWZas_ok {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us) (hw : VsWFit p d ws)
    (hp : 0 < p) : ∀ xt ∈ vsWZas d us ws, VsWPairOK p d d xt := by
  intro xt hxt
  simp only [vsWZas, List.mem_append, List.mem_map] at hxt
  rcases hxt with ⟨u, h1, rfl⟩ | ⟨w, h1, rfl⟩
  · exact ⟨(hu u h1).1, (hu u h1).1, (hu u h1).2, (hu u h1).2⟩
  · exact ⟨(hw w h1).1, fun y hy => by simp [vsWZ] at hy; omega, (hw w h1).2, by simp [vsWZ]⟩

/-- The pairs of the intersection span `{(x, t) | t ∈ U, x - t ∈ W}`. -/
theorem vsWZas_span {d : ℕ} (us ws : List (List ℕ)) (x t : ℕ → ZMod p) :
    (x, t) ∈ vsPairSpan p (vsWZas d us ws) ↔ t ∈ vsWSpN p us ∧ x - t ∈ vsWSpN p ws := by
  let S : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)) :=
    (vsWSpN p ws).comap (LinearMap.fst _ _ _ - LinearMap.snd _ _ _) ⊓
      (vsWSpN p us).comap (LinearMap.snd _ _ _)
  have hle : vsPairSpan p (vsWZas d us ws) ≤ S := by
    refine Submodule.span_le.mpr fun v hv => ?_
    simp only [vsWZas, List.map_append, List.map_map, Set.mem_setOf_eq, List.mem_append,
      List.mem_map, Function.comp_apply, vsP] at hv
    rcases hv with ⟨u, hu, rfl⟩ | ⟨w, hw, rfl⟩
    · refine ⟨?_, ?_⟩
      · simp [Submodule.zero_mem]
      · exact vsF_mem_vsWSpN hu
    · refine ⟨?_, ?_⟩
      · simp [vsWZ_vsF, vsF_mem_vsWSpN hw]
      · simp [vsWZ_vsF, Submodule.zero_mem]
  constructor
  · intro hm
    have := hle hm
    exact ⟨this.2, this.1⟩
  · rintro ⟨ht, hxt⟩
    have e : (x, t) = (LinearMap.id.prod LinearMap.id : (ℕ → ZMod p) →ₗ[ZMod p] _) t +
        LinearMap.inl (ZMod p) _ _ (x - t) := by
      ext <;> simp
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · have : (vsWSpN p us).map (LinearMap.id.prod LinearMap.id : (ℕ → ZMod p) →ₗ[ZMod p] _) ≤
          vsPairSpan p (vsWZas d us ws) := by
        rw [vsWSpN, Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine Submodule.subset_span ?_
        simp only [vsWZas, Set.mem_setOf_eq, List.map_append, List.mem_append, List.mem_map]
        exact Or.inl ⟨(u, u), ⟨u, hu, rfl⟩, rfl⟩
      exact this ⟨t, ht, rfl⟩
    · have : (vsWSpN p ws).map (LinearMap.inl (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p)) ≤
          vsPairSpan p (vsWZas d us ws) := by
        rw [vsWSpN, Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        refine Submodule.subset_span ?_
        simp only [vsWZas, Set.mem_setOf_eq, List.map_append, List.mem_append, List.mem_map]
        refine Or.inr ⟨(w, vsWZ d), ⟨w, hw, rfl⟩, ?_⟩
        simp [vsP, vsWZ_vsF]
      exact this ⟨x - t, hxt, rfl⟩

theorem vsWInter_spanN (hp : p.Prime) {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us)
    (hw : VsWFit p d ws) : vsWSpN p (vsWInter p d us ws) = vsWSpN p us ⊓ vsWSpN p ws := by
  ext s
  have hk := vsInsertAll_ker hp (fun xt hxt => (vsWZas_ok hu hw hp.pos xt hxt).below) s
  rw [vsWZas_span, zero_sub, neg_mem_iff] at hk
  rw [vsWSpN_eq_span_list, vsWInter, ← hk, Submodule.mem_inf]

theorem vsWInter_fit (hp : 0 < p) {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us)
    (hw : VsWFit p d ws) : VsWFit p d (vsWInter p d us ws) :=
  fun t ht => (vsWAcc_shape hp (vsWZas_ok hu hw hp)).rels t ht

/-- **Intersection.** -/
theorem vsWInter_span (hp : p.Prime) {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us)
    (hw : VsWFit p d ws) : vsWSp p d (vsWInter p d us ws) = vsWSp p d us ⊓ vsWSp p d ws := by
  rw [vsWSp_eq_map, vsWSp_eq_map, vsWSp_eq_map, vsWInter_spanN hp hu hw]
  exact vsWR_map_inf (vsWSpN_le_supp fun u h => (hu u h).2.le)
    (vsWSpN_le_supp fun u h => (hw u h).2.le)

/-! ### Images and the part in a kernel -/

/-- A `d × d` stored list. -/
def VsWSq (p d : ℕ) (A : List (List ℕ)) : Prop := VsWFit p d A ∧ A.length = d

theorem vsWImg_fit (hp : 0 < p) {d : ℕ} {A : List (List ℕ)} (hA : VsWSq p d A) (us : List (List ℕ)) :
    VsWFit p d (vsWImg p d A us) := by
  intro x hx
  simp only [vsWImg, List.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [vsFRowMul]
    exact vsFMulAcc_foldl_lt hp _ _ (fun y hy => by simp [vsWZ] at hy; omega)
  · rw [vsFRowMul, vsFMulAcc_foldl_length]
    simp [vsWZ]

/-- **Images.** -/
theorem vsWImg_span {d : ℕ} {A : List (List ℕ)} (hA : VsWSq p d A) (us : List (List ℕ)) :
    vsWSp p d (vsWImg p d A us) = (vsWSp p d us).map (vsWLin p d A) := by
  rw [vsWSp, vsWSp, Submodule.map_span]
  congr 1
  ext v
  simp only [vsWImg, List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, (vsWV_img hA.2 (fun r hr => (hA.1 r hr).2.le) u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, vsWV_img hA.2 (fun r hr => (hA.1 r hr).2.le) u⟩

theorem vsWCut_fit (hp : 0 < p) {d : ℕ} {us A : List (List ℕ)} :
    VsWFit p d (vsWCut p d us A) := by
  intro x hx
  simp only [vsWCut, List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [vsFRowMul]
    exact vsFMulAcc_foldl_lt hp _ _ (fun y hy => by simp [vsWZ] at hy; omega)
  · rw [vsFRowMul, vsFMulAcc_foldl_length]
    simp [vsWZ]

/-- **The part of a span in a kernel.** -/
theorem vsWCut_span (hp : p.Prime) {d : ℕ} {us A : List (List ℕ)} (hu : VsWFit p d us)
    (hA : VsWSq p d A) :
    vsWSp p d (vsWCut p d us A) = vsWSp p d us ⊓ LinearMap.ker (vsWLin p d A) := by
  have hI := vsWImg_fit hp.pos hA us
  have hlen : (vsWImg p d A us).length = us.length := by simp [vsWImg]
  have hcomp : ∀ a : Fin (vsWImg p d A us).length → ZMod p, vsWComb p d (vsWImg p d A us) a =
      vsWLin p d A (vsWComb p d us (fun i => a (Fin.cast hlen.symm i))) := by
    intro a
    rw [vsWComb_apply, vsWComb_apply, map_sum]
    refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
    simp only [map_smul, finCongr_apply]
    congr 1
    all_goals first
      | rfl
      | (have e : (vsWImg p d A us)[i] = vsFRowMul p (us[Fin.cast hlen i]) A (vsWZ d) := by
           simp only [vsWImg]; exact List.getElem_map ..
         rw [e]
         exact vsWV_img hA.2 (fun r hr => (hA.1 r hr).2.le) _)
  have hk := vsWKer_span hp hI
  have hmap : vsWSp p d (vsWCut p d us A) =
      (vsWSp p (vsWImg p d A us).length (vsWKer p (vsWImg p d A us))).map
        (vsWComb p d us ∘ₗ LinearMap.funLeft (ZMod p) (ZMod p) (Fin.cast hlen.symm)) := by
    rw [vsWSp, vsWSp, Submodule.map_span]
    congr 1
    ext v
    simp only [vsWCut, List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    have key : ∀ a, vsWV p d (vsFRowMul p a us (vsWZ d)) =
        (vsWComb p d us ∘ₗ LinearMap.funLeft (ZMod p) (ZMod p) (Fin.cast hlen.symm))
          (vsWV p (vsWImg p d A us).length a) := by
      intro a
      rw [vsWV_rowMul d a us (fun r hr => (hu r hr).2.le)]
      rfl
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, (key a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, key a⟩
  rw [hmap, hk, ← vsWComb_range]
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mem_inf, LinearMap.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [hcomp] at ha
    exact ha
  · rintro ⟨⟨b, rfl⟩, hb⟩
    refine ⟨fun i => b (Fin.cast hlen i), ?_, ?_⟩
    · rw [hcomp]; exact hb
    · rfl

/-! ### A stored matrix minus a scalar -/

/-- **Subtracting a scalar.** -/
theorem vsWSubC_matrix (hp : 0 < p) {d c : ℕ} (hc : c ≤ p) {A : List (List ℕ)} (hA : VsWSq p d A) :
    vsWM p d (vsWSubC p c A) = vsWM p d A - (c : ZMod p) • 1 := by
  obtain ⟨hf, hl⟩ := hA
  subst hl
  ext i j
  simp only [vsWM, Matrix.transpose_apply, vsFMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hj := j.2
  rw [vsWSubC, List.getD_eq_getElem _ _ (by simpa using j.2)]
  simp only [List.getElem_map, List.getElem_range]
  rw [vsF_vsLin _ _ _ (by rw [vsUnit_length, List.getD_eq_getElem _ _ j.2,
      (hf _ (List.getElem_mem j.2)).2]),
    vsF_vsUnit j.2, Nat.cast_sub hc, ZMod.natCast_self, List.getD_eq_getElem _ _ j.2]
  by_cases hij : j = i
  · subst hij; simp [sub_eq_add_neg]
  · have : (j : ℕ) ≠ i := fun h => hij (Fin.ext h)
    simp [Ne.symm this, Ne.symm hij]

theorem vsWSubC_fit (hp : 0 < p) {d c : ℕ} {A : List (List ℕ)} (hA : VsWSq p d A) :
    VsWSq p d (vsWSubC p c A) := by
  refine ⟨fun x hx => ?_, by simp [vsWSubC, hA.2]⟩
  simp only [vsWSubC, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  refine ⟨vsLin_lt hp _ _, ?_⟩
  rw [vsLin_length, List.getD_eq_getElem _ _ hj]
  exact (hA.1 _ (List.getElem_mem hj)).2

end GI.Proved
