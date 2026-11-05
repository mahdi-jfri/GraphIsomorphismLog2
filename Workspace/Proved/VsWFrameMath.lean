module

public import Workspace.Proved.VsWLinMath

@[expose] public section

/-!
# Frames

Let `W' ≤ W` be spans of lists `ws'` and `ws` in `𝔽_p^d`. We want to work on the quotient
`W / W'` with small `D × D` matrices. For that we choose vectors `c_0, …, c_{D-1}` (the list
`cs = vsWComp p ws' ws`) whose classes form a basis of `W / W'`. Every `x ∈ W` then has unique
local coordinates `a` with `x - ∑ a_j c_j ∈ W'` (`vsWCo_sub`, `vsWCo_unique`).

* `vsWFrame_sup`, `vsWFrame_indep`: the `c_j` together with `W'` span `W' ⊔ W`, and no nonzero
  combination of them lies in `W'`.
* `vsWCo_sub`, `vsWCo_unique`: local coordinates.
* `vsWLoc_co`: the local matrix of a matrix that maps `W'` and `W' ⊔ W` into themselves acts on
  local coordinates.
* `vsWLift_span`, `vsWLift_mem`: lifting a local span back to `𝔽_p^d`.

In the statements, `W' ⊔ W` appears instead of `W`, so `W' ≤ W` is never needed as a hypothesis.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

theorem vsWSpN_append (us ws : List (List ℕ)) :
    vsWSpN p (us ++ ws) = vsWSpN p us ⊔ vsWSpN p ws := by
  rw [vsWSpN, vsWSpN, vsWSpN, ← Submodule.span_union]
  congr 1
  ext v
  simp only [List.mem_append, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨u, hu | hu, rfl⟩
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr ⟨u, hu, rfl⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact ⟨u, Or.inl hu, rfl⟩
    · exact ⟨u, Or.inr hu, rfl⟩

theorem vsPairSpan_append' (L L' : List (List ℕ × List ℕ)) :
    vsPairSpan p (L ++ L') = vsPairSpan p L ⊔ vsPairSpan p L' := by
  rw [vsPairSpan, vsPairSpan, vsPairSpan, ← Submodule.span_union]
  congr 1
  ext v
  simp [List.map_append, or_comm]

/-- A vector of a span of a list is a combination of the list. -/
theorem vsWSpN_mem_iff (xs : List (List ℕ)) (v : ℕ → ZMod p) :
    v ∈ vsWSpN p xs ↔ ∃ b : ℕ → ZMod p,
      v = ∑ i ∈ Finset.range xs.length, b i • vsF p (xs.getD i []) := by
  have e : {w | ∃ u ∈ xs, vsF p u = w} = Set.range fun i : Fin xs.length => vsF p xs[i] := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, List.getElem_mem i.2, rfl⟩
  rw [vsWSpN, e, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => if h : i < xs.length then c ⟨i, h⟩ else 0, ?_⟩
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < xs.length then c ⟨i, h⟩ else 0) •
      vsF p (xs.getD i []))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2, List.getD_eq_getElem _ _ i.2]
  · rintro ⟨b, rfl⟩
    refine ⟨fun i => b i, ?_⟩
    rw [← Fin.sum_univ_eq_sum_range (fun i => b i • vsF p (xs.getD i []))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [List.getD_eq_getElem _ _ i.2]

/-! ### The complement -/

theorem vsWRows_prefix (hp : 0 < p) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) : vsWRows p ws' <+: vsWRows p (ws' ++ ws) := by
  have := vsWInsertAll_prefix hp (vsWPairs_ok h') (vsWPairs_ok h)
  simpa [vsWRows, vsWPairs, List.map_append] using this

theorem vsWFit_append {d : ℕ} {us ws : List (List ℕ)} (hu : VsWFit p d us) (hw : VsWFit p d ws) :
    VsWFit p d (us ++ ws) := fun x hx => by
  rcases List.mem_append.mp hx with h | h
  · exact hu x h
  · exact hw x h

/-- The rows of `ws' ++ ws` are those of `ws'` followed by the complement rows. -/
theorem vsWRows_split (hp : 0 < p) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) :
    vsWRows p (ws' ++ ws) = vsWRows p ws' ++ (vsWRows p (ws' ++ ws)).drop (vsWRows p ws').length := by
  obtain ⟨t, ht⟩ := vsWRows_prefix hp h' h
  conv_lhs => rw [← ht]
  rw [← ht, List.drop_left]

theorem vsWComp_fit (hp : 0 < p) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) : VsWFit p d (vsWComp p ws' ws) := by
  intro x hx
  simp only [vsWComp, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have := (vsWAcc_shape hp (vsWPairs_ok (vsWFit_append h' h))).rows r (List.mem_of_mem_drop hr)
  exact ⟨this.1, this.2.2.1⟩

theorem vsWFrame_supN (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) :
    vsWSpN p ws' ⊔ vsWSpN p (vsWComp p ws' ws) = vsWSpN p ws' ⊔ vsWSpN p ws := by
  have e1 := (vsWRows_inv hp (vsWFit_append h' h)).2.2
  have e2 := (vsWRows_inv hp h').2.2
  rw [vsWRows_split hp.pos h' h, vsSpan_eq_vsWSpN, List.map_append, vsWSpN_append,
    ← vsSpan_eq_vsWSpN, e2, vsWSpN_append] at e1
  exact e1

/-- **The complement and `W'` span `W' ⊔ W`.** -/
theorem vsWFrame_sup (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) :
    vsWSp p d ws' ⊔ vsWSp p d (vsWComp p ws' ws) = vsWSp p d ws' ⊔ vsWSp p d ws := by
  rw [vsWSp_eq_map, vsWSp_eq_map, vsWSp_eq_map, ← Submodule.map_sup, ← Submodule.map_sup,
    vsWFrame_supN hp h' h]

theorem vsW_mapD (L : List VsRow) (i : ℕ) :
    (L.map VsRow.x).getD i [] = (L.getD i ⟨0, [], []⟩).x := by
  rw [show ([] : List ℕ) = (⟨0, [], []⟩ : VsRow).x from rfl, List.getD_map]

/-- Echelon rows `R' ++ N`: a combination of `N` that is a combination of `R'` is trivial. -/
theorem vsWEch_split {R' N : List VsRow} (he : VsEch p (R' ++ N)) {a b : ℕ → ZMod p}
    (hb : ∑ j ∈ Finset.range N.length, a j • vsF p ((N.map VsRow.x).getD j []) =
      ∑ i ∈ Finset.range R'.length, b i • vsF p ((R'.map VsRow.x).getD i [])) :
    ∀ j < N.length, a j = 0 := by
  let g : ℕ → ZMod p := fun i => if i < R'.length then -b i else a (i - R'.length)
  have hz : ∑ i ∈ Finset.range (R' ++ N).length, g i • vsF p ((R' ++ N).getD i ⟨0, [], []⟩).x = 0 := by
    rw [List.length_append, Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range R'.length, g i • vsF p ((R' ++ N).getD i ⟨0, [], []⟩).x =
        -∑ i ∈ Finset.range R'.length, b i • vsF p ((R'.map VsRow.x).getD i []) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [g, hi', if_true, neg_smul]
      rw [List.getD_append _ _ _ _ hi', vsW_mapD]
    have h2 : ∑ i ∈ Finset.range N.length, g (R'.length + i) •
        vsF p ((R' ++ N).getD (R'.length + i) ⟨0, [], []⟩).x =
        ∑ j ∈ Finset.range N.length, a j • vsF p ((N.map VsRow.x).getD j []) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [g, show ¬ R'.length + i < R'.length by omega, if_false, Nat.add_sub_cancel_left]
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, vsW_mapD]
    rw [h1, h2, hb, neg_add_cancel]
  intro j hj
  have := vsWEch_indep he hz (R'.length + j) (by simp; omega)
  simpa [g] using this

/-- The ℕ-level combination of the complement with coefficients `a`. -/
theorem vsWFrame_indepN (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) {a : ℕ → ZMod p}
    (ha : ∑ j ∈ Finset.range (vsWComp p ws' ws).length,
      a j • vsF p ((vsWComp p ws' ws).getD j []) ∈ vsWSpN p ws') :
    ∀ j < (vsWComp p ws' ws).length, a j = 0 := by
  have he := (vsWRows_inv hp (vsWFit_append h' h)).1
  have hsplit := vsWRows_split hp.pos h' h
  have e2 := (vsWRows_inv hp h').2.2
  rw [← e2, vsSpan_eq_vsWSpN, vsWSpN_mem_iff] at ha
  obtain ⟨b, hb⟩ := ha
  rw [hsplit] at he
  have hl : (vsWComp p ws' ws).length =
      ((vsWRows p (ws' ++ ws)).drop (vsWRows p ws').length).length := by simp [vsWComp]
  intro j hj
  rw [hl] at hj
  refine vsWEch_split he (b := b) ?_ j hj
  rw [List.length_map] at hb
  rw [← hb, hl]
  rfl

/-- The ℕ-level combination of a list, restricted, is `vsWComb`. -/
theorem vsWR_sum (d : ℕ) (xs : List (List ℕ)) (a : ℕ → ZMod p) :
    vsWR p d (∑ j ∈ Finset.range xs.length, a j • vsF p (xs.getD j [])) =
      vsWComb p d xs (vsWR p xs.length a) := by
  have := vsWR_vsComb (p := p) d xs a
  rw [vsComb] at this
  exact this

/-- **The complement is independent modulo `W'`.** -/
theorem vsWFrame_indep (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) {a : Fin (vsWComp p ws' ws).length → ZMod p}
    (ha : vsWComb p d (vsWComp p ws' ws) a ∈ vsWSp p d ws') : a = 0 := by
  have hc := vsWComp_fit hp.pos h' h
  rw [← vsWR_vsWE _ a, ← vsWR_sum, vsWSp_eq_map] at ha
  obtain ⟨f, hf, he⟩ := ha
  have hs := vsWSum_supp (d := d) (xs := vsWComp p ws' ws) (fun x hx => (hc x hx).2.le)
    (vsWE p (vsWComp p ws' ws).length a)
  rw [vsWR_injOn ((vsWSpN_le_supp fun w hw => (h' w hw).2.le) hf) hs he] at hf
  have := vsWFrame_indepN hp h' h hf
  funext j
  have := this j j.2
  rwa [vsWE_apply_lt] at this

/-! ### Local coordinates -/

theorem vsWFrPairs_ok (hp : 1 < p) {d : ℕ} {ws' cs : List (List ℕ)} (h' : VsWFit p d ws')
    (hc : VsWFit p d cs) : ∀ xt ∈ vsWFrPairs ws' cs, VsWPairOK p d cs.length xt := by
  intro xt hxt
  rcases List.mem_append.mp hxt with hx | hx
  · simp only [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨(h' w hw).1, fun y hy => by simp [vsWZ] at hy; omega, (h' w hw).2, by simp [vsWZ]⟩
  · exact vsWUnitPairs_ok hc hp xt hx

/-- The frame pairs lie in `{(x, t) | x - ∑ t_j c_j ∈ W'}`. -/
theorem vsWFrPairs_span {ws' cs : List (List ℕ)} {x t : ℕ → ZMod p}
    (h : (x, t) ∈ vsPairSpan p (vsWFrPairs ws' cs)) : x - vsComb p cs t ∈ vsWSpN p ws' := by
  rw [vsWFrPairs, vsPairSpan_append', Submodule.mem_sup] at h
  obtain ⟨v1, h1, v2, h2, he⟩ := h
  have hle : vsPairSpan p (ws'.map fun w => (w, vsWZ cs.length)) ≤ (vsWSpN p ws').prod ⊥ := by
    refine Submodule.span_le.mpr fun v hv => ?_
    simp only [Set.mem_setOf_eq, List.map_map, List.mem_map, Function.comp_apply, vsP] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨vsF_mem_vsWSpN hw, by simp [vsWZ_vsF]⟩
  obtain ⟨hv1, hv1'⟩ := hle h1
  replace hv1' : v1.2 = 0 := by simpa using hv1'
  have hv2 := ((vsUnitPairs_span cs v2.1 v2.2).mp (by rw [← Prod.mk.eta (p := v2)] at h2; exact h2)).2
  have ex : x = v1.1 + v2.1 := by have := congrArg Prod.fst he; simpa using this.symm
  have et : t = v2.2 := by have := congrArg Prod.snd he; simpa [hv1'] using this.symm
  rw [ex, et, ← hv2, add_sub_cancel_right]
  exact hv1

theorem vsWFrRows_inv (hp : p.Prime) {d : ℕ} {ws' cs : List (List ℕ)} (h' : VsWFit p d ws')
    (hc : VsWFit p d cs) :
    vsSpan p (vsWFrRows p ws' cs) = vsWSpN p ws' ⊔ vsWSpN p cs := by
  rw [vsWFrRows, vsInsertAll_span hp (fun xt hxt => (vsWFrPairs_ok hp.one_lt h' hc xt hxt).below),
    ← vsWSpN_append, vsWSpN_eq_span_list, vsWFrPairs, List.map_append, List.map_map,
    vsWUnitPairs_main, List.map_append]
  rfl

theorem vsWCo_fit (hp : 0 < p) (ws' cs : List (List ℕ)) (x : List ℕ) :
    VsWFit p cs.length [vsWCo p ws' cs x] := by
  intro y hy
  simp only [List.mem_singleton] at hy
  subst hy
  refine ⟨vsWNeg_lt hp _, ?_⟩
  rw [vsWCo, vsWNeg_length, (vsSift_length _ _ _).2]
  simp [vsWZ]

/-- **Local coordinates.** For `x ∈ W' ⊔ W`, `x - ∑ a_j c_j ∈ W'` with `a = vsWCo x`. -/
theorem vsWCo_sub (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) {x : List ℕ} (hx : VsWFit p d [x])
    (hW : vsWV p d x ∈ vsWSp p d ws' ⊔ vsWSp p d ws) :
    vsWV p d x - vsWComb p d (vsWComp p ws' ws)
      (vsWV p (vsWComp p ws' ws).length (vsWCo p ws' (vsWComp p ws' ws) x)) ∈ vsWSp p d ws' := by
  have hc := vsWComp_fit hp.pos h' h
  have hxf := hx x (List.mem_singleton_self _)
  have hL := fun xt hxt => (vsWFrPairs_ok hp.one_lt h' hc xt hxt).below
  have hs := vsSolve hp hL hxf.1 hxf.2 (z := vsWZ (vsWComp p ws' ws).length) (by simp [vsWZ]) (vsWZ_vsF _)
  have hsupW : vsWSpN p ws' ⊔ vsWSpN p ws ≤ vsWSupp p d :=
    sup_le (vsWSpN_le_supp fun w hw => (h' w hw).2.le) (vsWSpN_le_supp fun w hw => (h w hw).2.le)
  have hxN : vsF p x ∈ vsWSpN p ws' ⊔ vsWSpN p ws := by
    rw [vsWSp_eq_map, vsWSp_eq_map, ← Submodule.map_sup] at hW
    obtain ⟨f, hf, he⟩ := hW
    rwa [← vsWR_injOn (hsupW hf) (vsF_mem_vsWSupp hxf.2.le) he]
  rw [← vsWFrame_supN hp h' h, ← vsWFrRows_inv hp h' hc] at hxN
  have h0 := hs.1.mpr hxN
  have hm := vsWFrPairs_span (hs.2 h0)
  have e : vsWV p (vsWComp p ws' ws).length (vsWCo p ws' (vsWComp p ws' ws) x) =
      vsWR p (vsWComp p ws' ws).length (-vsF p (vsSift p (vsInsertAll p (vsWFrPairs ws'
        (vsWComp p ws' ws))).1 (x, vsWZ (vsWComp p ws' ws).length)).2) := by
    rw [vsWV, vsWCo, vsWNeg_vsF hp.pos]; rfl
  rw [e, ← vsWR_vsComb, vsWSp_eq_map]
  exact ⟨_, hm, by rw [map_sub]; rfl⟩

/-- **Local coordinates are unique.** -/
theorem vsWCo_unique (hp : p.Prime) {d : ℕ} {ws' ws : List (List ℕ)} (h' : VsWFit p d ws')
    (h : VsWFit p d ws) {v : Fin d → ZMod p} {a b : Fin (vsWComp p ws' ws).length → ZMod p}
    (ha : v - vsWComb p d (vsWComp p ws' ws) a ∈ vsWSp p d ws')
    (hb : v - vsWComb p d (vsWComp p ws' ws) b ∈ vsWSp p d ws') : a = b := by
  have := Submodule.sub_mem _ hb ha
  rw [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp (vsWFrame_indep hp h' h this)

end GI.Proved
