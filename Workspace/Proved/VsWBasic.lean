import Workspace.Impl.VsWDefs
import Workspace.Proved.VStabLinUnitMath
import Workspace.Proved.VsFMatMath
import Workspace.Proved.VsFMatPowMath

/-!
# Readings of lists as vectors, spans and matrices

The L0 lemmas read a list `x` as `vsF p x : ℕ → ZMod p`. The vector stabilizer states its problems on
`Fin d → ZMod p`. A vector of length at most `d` reads as a function that is `0` from `d` on,
so nothing is lost by restricting to `Fin d` (`vsWR`). This file gives the readings and the
first facts that move statements between the two settings.

* `vsWV`, `vsWSp`, `vsWM`, `vsWLin`, `vsWComb`: the readings of vectors, spanning lists, stored
  matrices and combinations.
* `vsWSupp`: the vectors that are `0` from `d` on. On it, restriction is injective
  (`vsWR_injOn`), so it commutes with intersections (`vsWR_map_inf`).
* `vsWEch_indep`: echelon rows are linearly independent.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-! ### Restriction and extension by zero -/

/-- Restriction of a vector to the first `d` coordinates. -/
def vsWR (p d : ℕ) : (ℕ → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) (fun j : Fin d => (j : ℕ))

@[simp] theorem vsWR_apply (d : ℕ) (f : ℕ → ZMod p) (j : Fin d) : vsWR p d f j = f j := rfl

/-- Extension by zero. -/
def vsWE (p d : ℕ) : (Fin d → ZMod p) →ₗ[ZMod p] (ℕ → ZMod p) where
  toFun v j := if h : j < d then v ⟨j, h⟩ else 0
  map_add' v w := by
    funext j
    by_cases h : j < d <;> simp [h]
  map_smul' c v := by
    funext j
    by_cases h : j < d <;> simp [h]

theorem vsWE_apply_lt {d : ℕ} (v : Fin d → ZMod p) {j : ℕ} (h : j < d) : vsWE p d v j = v ⟨j, h⟩ := by
  simp [vsWE, h]

theorem vsWR_vsWE (d : ℕ) (v : Fin d → ZMod p) : vsWR p d (vsWE p d v) = v := by
  funext j
  simp [vsWE, j.2]

/-- The vectors that are `0` from `d` on. -/
def vsWSupp (p d : ℕ) : Submodule (ZMod p) (ℕ → ZMod p) where
  carrier := {f | ∀ j, d ≤ j → f j = 0}
  add_mem' ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' _ _ := rfl
  smul_mem' c f hf j hj := by simp [hf j hj]

theorem mem_vsWSupp {d : ℕ} {f : ℕ → ZMod p} : f ∈ vsWSupp p d ↔ ∀ j, d ≤ j → f j = 0 := Iff.rfl

theorem vsWE_vsWR {d : ℕ} {f : ℕ → ZMod p} (hf : f ∈ vsWSupp p d) : vsWE p d (vsWR p d f) = f := by
  funext j
  by_cases h : j < d
  · simp [vsWE, h]
  · simp [vsWE, h, hf j (by omega)]

theorem vsWE_mem (d : ℕ) (v : Fin d → ZMod p) : vsWE p d v ∈ vsWSupp p d := fun j hj => by
  simp [vsWE, show ¬ j < d by omega]

theorem vsF_mem_vsWSupp {d : ℕ} {x : List ℕ} (hx : x.length ≤ d) : vsF p x ∈ vsWSupp p d :=
  fun j hj => by rw [vsF_apply, List.getD_eq_default _ _ (show x.length ≤ j by omega)]; simp

theorem vsWR_injOn {d : ℕ} {f g : ℕ → ZMod p} (hf : f ∈ vsWSupp p d) (hg : g ∈ vsWSupp p d)
    (h : vsWR p d f = vsWR p d g) : f = g := by
  rw [← vsWE_vsWR hf, ← vsWE_vsWR hg, h]

theorem vsWR_eq_zero {d : ℕ} {f : ℕ → ZMod p} (hf : f ∈ vsWSupp p d) (h : vsWR p d f = 0) :
    f = 0 :=
  vsWR_injOn hf (Submodule.zero_mem _) (by rw [h, map_zero])

/-- Restriction is injective on submodules of `vsWSupp`. -/
theorem vsWR_map_inj {d : ℕ} {S T : Submodule (ZMod p) (ℕ → ZMod p)} (hS : S ≤ vsWSupp p d)
    (hT : T ≤ vsWSupp p d) (h : S.map (vsWR p d) = T.map (vsWR p d)) : S = T := by
  have key : ∀ {S T : Submodule (ZMod p) (ℕ → ZMod p)}, S ≤ vsWSupp p d → T ≤ vsWSupp p d →
      S.map (vsWR p d) ≤ T.map (vsWR p d) → S ≤ T := by
    intro S T hS hT h f hf
    obtain ⟨g, hg, he⟩ := h ⟨f, hf, rfl⟩
    rwa [vsWR_injOn (hT hg) (hS hf) he] at hg
  exact le_antisymm (key hS hT h.le) (key hT hS h.ge)

/-- Restriction commutes with intersections inside `vsWSupp`. -/
theorem vsWR_map_inf {d : ℕ} {S T : Submodule (ZMod p) (ℕ → ZMod p)} (hS : S ≤ vsWSupp p d)
    (hT : T ≤ vsWSupp p d) : (S ⊓ T).map (vsWR p d) = S.map (vsWR p d) ⊓ T.map (vsWR p d) := by
  refine le_antisymm (Submodule.map_inf_le _) ?_
  rintro v ⟨⟨f, hf, rfl⟩, ⟨g, hg, he⟩⟩
  rw [vsWR_injOn (hT hg) (hS hf) he] at hg
  exact ⟨f, ⟨hf, hg⟩, rfl⟩

/-! ### Readings -/

/-- A list read as a vector of `𝔽_p^d`. -/
def vsWV (p d : ℕ) (x : List ℕ) : Fin d → ZMod p := vsWR p d (vsF p x)

@[simp] theorem vsWV_apply (d : ℕ) (x : List ℕ) (j : Fin d) : vsWV p d x j = vsF p x j := rfl

/-- The span of the vectors of a list, in `ℕ → ZMod p`. -/
def vsWSpN (p : ℕ) (us : List (List ℕ)) : Submodule (ZMod p) (ℕ → ZMod p) :=
  Submodule.span (ZMod p) {v | ∃ u ∈ us, vsF p u = v}

/-- The span of the vectors of a list, in `𝔽_p^d`. -/
def vsWSp (p d : ℕ) (us : List (List ℕ)) : Submodule (ZMod p) (Fin d → ZMod p) :=
  Submodule.span (ZMod p) {v | ∃ u ∈ us, vsWV p d u = v}

theorem vsWSp_eq_map (d : ℕ) (us : List (List ℕ)) : vsWSp p d us = (vsWSpN p us).map (vsWR p d) := by
  rw [vsWSp, vsWSpN, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

theorem vsWSp_append (d : ℕ) (us ws : List (List ℕ)) :
    vsWSp p d (us ++ ws) = vsWSp p d us ⊔ vsWSp p d ws := by
  rw [vsWSp, vsWSp, vsWSp, ← Submodule.span_union]
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

theorem vsF_mem_vsWSpN {us : List (List ℕ)} {u : List ℕ} (hu : u ∈ us) : vsF p u ∈ vsWSpN p us :=
  Submodule.subset_span ⟨u, hu, rfl⟩

theorem vsWV_mem_vsWSp (d : ℕ) {us : List (List ℕ)} {u : List ℕ} (hu : u ∈ us) :
    vsWV p d u ∈ vsWSp p d us :=
  Submodule.subset_span ⟨u, hu, rfl⟩

/-- A list of vectors of length `d` with entries below `p`. -/
def VsWFit (p d : ℕ) (us : List (List ℕ)) : Prop := ∀ u ∈ us, (∀ y ∈ u, y < p) ∧ u.length = d

theorem vsWSpN_le_supp {d : ℕ} {us : List (List ℕ)} (h : ∀ u ∈ us, u.length ≤ d) :
    vsWSpN p us ≤ vsWSupp p d :=
  Submodule.span_le.mpr fun _ ⟨u, hu, he⟩ => he ▸ vsF_mem_vsWSupp (h u hu)

/-- Equal spans in `𝔽_p^d` exactly when equal spans in `ℕ → ZMod p`. -/
theorem vsWSp_eq_iff {d : ℕ} {us ws : List (List ℕ)} (hu : ∀ u ∈ us, u.length ≤ d)
    (hw : ∀ w ∈ ws, w.length ≤ d) : vsWSp p d us = vsWSp p d ws ↔ vsWSpN p us = vsWSpN p ws := by
  rw [vsWSp_eq_map, vsWSp_eq_map]
  exact ⟨vsWR_map_inj (vsWSpN_le_supp hu) (vsWSpN_le_supp hw), fun h => by rw [h]⟩

/-- The matrix a stored list stands for: the transpose of the matrix of its rows. -/
def vsWM (p d : ℕ) (A : List (List ℕ)) : Matrix (Fin d) (Fin d) (ZMod p) := Matrix.transpose (vsFMatrix p d A)

/-- The linear map of a stored list. -/
noncomputable def vsWLin (p d : ℕ) (A : List (List ℕ)) :
    Module.End (ZMod p) (Fin d → ZMod p) := Matrix.toLin' (vsWM p d A)

/-- The combination `a ↦ ∑ a_i u_i`. -/
noncomputable def vsWComb (p d : ℕ) (us : List (List ℕ)) :
    (Fin us.length → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
  Fintype.linearCombination (ZMod p) fun i => vsWV p d us[i]

theorem vsWComb_apply (d : ℕ) (us : List (List ℕ)) (a : Fin us.length → ZMod p) :
    vsWComb p d us a = ∑ i, a i • vsWV p d us[i] := by
  simp [vsWComb, Fintype.linearCombination_apply]

theorem vsWComb_range (d : ℕ) (us : List (List ℕ)) :
    LinearMap.range (vsWComb p d us) = vsWSp p d us := by
  rw [vsWComb, Fintype.range_linearCombination, vsWSp]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, List.getElem_mem i.2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    exact ⟨⟨i, hi⟩, rfl⟩

/-- The L0 combination `vsComb`, restricted, is `vsWComb` of the restricted coefficients. -/
theorem vsWR_vsComb (d : ℕ) (us : List (List ℕ)) (a : ℕ → ZMod p) :
    vsWR p d (vsComb p us a) = vsWComb p d us (vsWR p us.length a) := by
  rw [vsWComb_apply, vsComb, map_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => vsWR p d (a i • vsF p (us.getD i [])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, List.getD_eq_getElem _ _ i.2]
  rfl

/-- A row of the product program is the combination of the rows of `A` (`|a| ≥ |A|` not needed:
only the entries of `a` below `|A|` are read). -/
theorem vsWV_rowMul (d : ℕ) (a : List ℕ) (A : List (List ℕ)) (hA : ∀ r ∈ A, r.length ≤ d) :
    vsWV p d (vsFRowMul p a A (vsWZ d)) = vsWComb p d A (vsWV p A.length a) := by
  have h := vsFMat_rowMul p a A (vsWZ d) (by simpa [vsWZ] using hA)
  have hz : vsF p (vsWZ d) = 0 := by funext j; simp [vsF, vsWZ, List.getD_eq_getElem?_getD]
  rw [hz, zero_add] at h
  rw [vsWV, h, vsWComb_apply, map_sum, ← Fin.sum_univ_eq_sum_range
    (fun j => vsWR p d (((a.getD j 0 : ℕ) : ZMod p) • vsF p (A.getD j [])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, List.getD_eq_getElem _ _ i.2]
  rfl

/-- The linear map of a stored `d × d` list is the combination of its rows. -/
theorem vsWLin_apply {d : ℕ} {A : List (List ℕ)} (hA : A.length = d) (v : Fin d → ZMod p) :
    vsWLin p d A v = vsWComb p d A (fun i => v (Fin.cast hA i)) := by
  subst hA
  funext i
  rw [vsWLin, Matrix.toLin'_apply, vsWComb_apply, Matrix.mulVec, Finset.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [vsWM, Matrix.transpose_apply, vsFMatrix, Pi.smul_apply, smul_eq_mul,
    vsWV_apply, Fin.cast_eq_self]
  rw [List.getD_eq_getElem _ _ j.2, mul_comm]
  rfl

/-- The image of a vector under a stored `d × d` list, as the product program computes it. -/
theorem vsWV_img {d : ℕ} {A : List (List ℕ)} (hA : A.length = d) (hAr : ∀ r ∈ A, r.length ≤ d)
    (u : List ℕ) : vsWV p d (vsFRowMul p u A (vsWZ d)) = vsWLin p d A (vsWV p d u) := by
  rw [vsWV_rowMul d u A hAr, vsWLin_apply hA]
  rfl

/-! ### Echelon rows are independent -/

/-- **Echelon rows are independent.** If `∑_{i < |rows|} g_i x_i = 0` for echelon rows, then
every `g_i` with `i < |rows|` is `0`. -/
theorem vsWEch_indep {rows : List VsRow} (he : VsEch p rows) {g : ℕ → ZMod p}
    (hg : ∑ i ∈ Finset.range rows.length, g i • vsF p (rows.getD i ⟨0, [], []⟩).x = 0) :
    ∀ i < rows.length, g i = 0 := by
  induction rows generalizing g with
  | nil => intro i hi; simp at hi
  | cons r rs ih =>
    obtain ⟨h1, h0, hrs⟩ := he
    rw [List.length_cons, Finset.sum_range_succ'] at hg
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hg
    have hrest : ∀ i < rs.length, vsF p (rs.getD i ⟨0, [], []⟩).x r.j = 0 := fun i hi => by
      rw [List.getD_eq_getElem _ _ hi]; exact h0 _ (List.getElem_mem hi)
    have hg0 : g 0 = 0 := by
      have := congrFun hg r.j
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        h1, mul_one] at this
      rwa [Finset.sum_eq_zero fun i hi => by rw [hrest i (Finset.mem_range.mp hi), mul_zero],
        zero_add] at this
    rw [hg0, zero_smul, add_zero] at hg
    have := ih hrs (g := fun i => g (i + 1)) hg
    intro i hi
    rcases i with _ | i
    · exact hg0
    · exact this i (by simp at hi; omega)

/-! ### Facts about the insertion -/

theorem vsWPairs_fit {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    ∀ xt ∈ vsWPairs us, VsBelow p xt ∧ xt.1.length = d ∧ xt.2.length = 0 := by
  intro xt hxt
  simp only [vsWPairs, List.mem_map] at hxt
  obtain ⟨u, hu, rfl⟩ := hxt
  exact ⟨(h u hu).1, (h u hu).2, rfl⟩

theorem vsWPairs_main (us : List (List ℕ)) :
    (vsWPairs us).map (fun xt => vsF p xt.1) = us.map (vsF p) := by
  simp [vsWPairs]

theorem vsWSpN_eq_span_list (us : List (List ℕ)) :
    vsWSpN p us = Submodule.span (ZMod p) {w | w ∈ us.map (vsF p)} := by
  rw [vsWSpN]; congr 1; ext v; simp

/-- The rows of `vsWRows` are echelon, of length `d`, and span the vectors. -/
theorem vsWRows_inv (hp : p.Prime) {d : ℕ} {us : List (List ℕ)} (h : VsWFit p d us) :
    VsEch p (vsWRows p us) ∧ (∀ r ∈ vsWRows p us, r.x.length = d) ∧
      vsSpan p (vsWRows p us) = vsWSpN p us := by
  have hI := vsInsertAll_inv hp (vsWPairs_fit h)
  refine ⟨hI.ech, fun r hr => (hI.len r hr).1, ?_⟩
  rw [vsWRows, vsInsertAll_span hp (vsWPairs_fit h), vsWPairs_main, vsWSpN_eq_span_list]

theorem vsSpan_eq_vsWSpN (rows : List VsRow) : vsSpan p rows = vsWSpN p (rows.map VsRow.x) := by
  rw [vsSpan, vsWSpN_eq_span_list, List.map_map]
  rfl

end GI.Proved
