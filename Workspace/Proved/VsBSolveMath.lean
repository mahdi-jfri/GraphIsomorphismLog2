import Workspace.Proved.VsWLinMath
import Workspace.Impl.VStabLinInsert

/-!
# Solving `∑ a_i v_i = u` by a kernel

To write a vector `u` of the span of `v_0, …, v_{m-1}` as a combination, take the relations
`K` among `v_0, …, v_{m-1}, u` (`vsWKer`). Some relation `r` has `r_m ≠ 0` (the relation
`(a, -1)` is in the span of `K`), and then `a = -r_m⁻¹ r` works.

* `vsBSolveL p vs u`: the coefficients (a list of length `m + 1`; the last entry is not used).
* `vsBSolve_found`, `vsBSolve_comb`.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-- The index of the first relation with a nonzero last entry. -/
def vsBSolveIdx (p : ℕ) (vs : List (List ℕ)) (u : List ℕ) : ℕ :=
  (vsWKer p (vs ++ [u])).findIdx fun r => decide (0 < r.getD vs.length 0)

/-- That relation. -/
def vsBSolveR (p : ℕ) (vs : List (List ℕ)) (u : List ℕ) : List ℕ :=
  (vsWKer p (vs ++ [u])).getD (vsBSolveIdx p vs u) []

/-- The coefficients `-r_m⁻¹ r`. -/
def vsBSolveL (p : ℕ) (vs : List (List ℕ)) (u : List ℕ) : List ℕ :=
  vsLin p (p - vsInv p ((vsBSolveR p vs u).getD vs.length 0)) 0 (vsBSolveR p vs u) (vsBSolveR p vs u)

section

variable (hp : p.Prime) {d : ℕ} {vs : List (List ℕ)} (hvs : VsWFit p d vs) {u : List ℕ}
  (hu : VsWFit p d [u]) (hsp : vsWV p d u ∈ vsWSp p d vs)
include hp hvs hu hsp

theorem vsBSolve_found : vsBSolveIdx p vs u < (vsWKer p (vs ++ [u])).length := by
  haveI := Fact.mk hp
  by_contra hno
  push Not at hno
  have hall : ∀ r ∈ vsWKer p (vs ++ [u]), r.getD vs.length 0 = 0 := by
    intro r hr
    by_contra hne
    have hlt : (vsWKer p (vs ++ [u])).findIdx (fun r => decide (0 < r.getD vs.length 0)) <
        (vsWKer p (vs ++ [u])).length :=
      List.findIdx_lt_length_of_exists ⟨r, hr, by simpa using Nat.pos_of_ne_zero hne⟩
    exact absurd hlt (not_lt.mpr (by simpa [vsBSolveIdx] using hno))
  have hfit : VsWFit p d (vs ++ [u]) := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hvs x hx
    · exact hu x hx
  have hker := vsWKer_span hp hfit
  set m := vs.length
  have hlen : (vs ++ [u]).length = m + 1 := by simp [m]
  -- the last coordinate vanishes on the span of the relations
  let ℓ : (Fin (vs ++ [u]).length → ZMod p) →ₗ[ZMod p] ZMod p :=
    LinearMap.proj (⟨m, by omega⟩ : Fin (vs ++ [u]).length)
  have hle : vsWSp p (vs ++ [u]).length (vsWKer p (vs ++ [u])) ≤ LinearMap.ker ℓ := by
    rw [vsWSp, Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ℓ, LinearMap.proj_apply, vsWV_apply, vsF]
    rw [hall r hr]; simp
  -- the relation `(a, -1)`
  obtain ⟨a, ha⟩ : ∃ a : Fin m → ZMod p, ∑ i, a i • vsWV p d vs[i] = vsWV p d u := by
    rw [← vsWComb_range] at hsp
    obtain ⟨a, ha⟩ := hsp
    exact ⟨a, by rw [← ha, vsWComb_apply]⟩
  set F : ℕ → (Fin d → ZMod p) := fun k =>
    (if h : k < m then a ⟨k, h⟩ else -1) • vsWV p d ((vs ++ [u]).getD k [])
  let x : Fin (vs ++ [u]).length → ZMod p := fun i => if h : (i : ℕ) < m then a ⟨i, h⟩ else -1
  have hx0 : vsWComb p d (vs ++ [u]) x = 0 := by
    rw [vsWComb_apply]
    have e1 : ∀ i : Fin (vs ++ [u]).length, x i • vsWV p d (vs ++ [u])[i] = F i := by
      intro i
      simp only [x, F, List.getD_eq_getElem _ _ i.2]
      rfl
    simp only [e1]
    rw [Fin.sum_univ_eq_sum_range F, hlen, Finset.sum_range_succ]
    rw [← Fin.sum_univ_eq_sum_range F m]
    have e2 : ∀ i : Fin m, F i = a i • vsWV p d vs[i] := by
      intro i
      simp only [F, dif_pos i.2, Fin.eta]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left i.2]
      rfl
    simp only [e2, ha]
    have e3 : F m = -vsWV p d u := by
      simp only [F, lt_irrefl, dif_neg (not_false), neg_one_smul]
      rw [List.getD_eq_getElem _ _ (by simp [m]), List.getElem_append_right (le_refl _)]
      simp [m]
    rw [e3, add_neg_cancel]
  have hxK : x ∈ vsWSp p (vs ++ [u]).length (vsWKer p (vs ++ [u])) := by
    rw [hker]; exact hx0
  have := hle hxK
  rw [LinearMap.mem_ker] at this
  simp only [ℓ, LinearMap.proj_apply, x, lt_irrefl, dif_neg (not_false)] at this
  exact one_ne_zero (neg_eq_zero.mp this)

omit hp hvs hu hsp in
theorem vsB_comb_split (z : List ℕ) :
    vsWComb p d (vs ++ [u]) (vsWV p (vs ++ [u]).length z) =
      ∑ i : Fin vs.length, vsF p z i • vsWV p d vs[i] + vsF p z vs.length • vsWV p d u := by
  rw [vsWComb_apply]
  set m := vs.length
  set F : ℕ → (Fin d → ZMod p) := fun k => vsF p z k • vsWV p d ((vs ++ [u]).getD k [])
  have e1 : ∀ i : Fin (vs ++ [u]).length, vsWV p (vs ++ [u]).length z i • vsWV p d (vs ++ [u])[i] = F i := by
    intro i
    simp only [vsWV_apply, F, List.getD_eq_getElem _ _ i.2]
    rfl
  simp only [e1]
  have hlen : (vs ++ [u]).length = m + 1 := by simp [m]
  rw [Fin.sum_univ_eq_sum_range F, hlen, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range F m]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left i.2]
    rfl
  · simp only [F]
    rw [List.getD_eq_getElem _ _ (by simp [m]), List.getElem_append_right (le_refl _)]
    simp [m]

theorem vsBSolve_comb :
    (∀ y ∈ vsBSolveL p vs u, y < p) ∧ (vsBSolveL p vs u).length = vs.length + 1 ∧
      ∑ i : Fin vs.length, vsF p (vsBSolveL p vs u) i • vsWV p d vs[i] = vsWV p d u := by
  haveI := Fact.mk hp
  have hfound := vsBSolve_found hp hvs hu hsp
  have hfit : VsWFit p d (vs ++ [u]) := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hvs x hx
    · exact hu x hx
  set K := vsWKer p (vs ++ [u])
  set r := vsBSolveR p vs u
  have hrK : r ∈ K := by
    simp only [r, vsBSolveR]
    rw [List.getD_eq_getElem _ _ hfound]
    exact List.getElem_mem _
  have hrfit := vsWKer_fit hp.one_lt hfit r hrK
  have hrl : r.length = vs.length + 1 := by rw [hrfit.2]; simp
  have hpos : 0 < r.getD vs.length 0 := by
    have hf' : K.findIdx (fun r => decide (0 < r.getD vs.length 0)) < K.length := hfound
    have := List.findIdx_getElem (xs := K) (p := fun r => decide (0 < r.getD vs.length 0)) (w := hf')
    simp only [decide_eq_true_eq] at this
    simp only [r, vsBSolveR]
    rw [List.getD_eq_getElem _ _ hfound]
    exact this
  have hrm : r.getD vs.length 0 < p := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hrfit.1 _ (List.getElem_mem _)
  obtain ⟨hci, hcir⟩ := vsInv_correct hp hpos hrm
  set ci := vsInv p (r.getD vs.length 0)
  have hker : vsWComb p d (vs ++ [u]) (vsWV p (vs ++ [u]).length r) = 0 := by
    have : vsWV p (vs ++ [u]).length r ∈ vsWSp p (vs ++ [u]).length K :=
      Submodule.subset_span ⟨r, hrK, rfl⟩
    rw [vsWKer_span hp hfit] at this
    exact this
  rw [vsB_comb_split] at hker
  have hrm' : vsF p r vs.length = (r.getD vs.length 0 : ZMod p) := rfl
  have hinv : (ci : ZMod p) * (r.getD vs.length 0 : ZMod p) = 1 := by
    have := congrArg (fun k : ℕ => (k : ZMod p)) hcir
    simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at this
    exact this
  have hpc : ((p - ci : ℕ) : ZMod p) = -(ci : ZMod p) := by
    rw [Nat.cast_sub hci.le, ZMod.natCast_self, zero_sub]
  have hla : ∀ i, vsF p (vsBSolveL p vs u) i = -(ci : ZMod p) * vsF p r i := by
    intro i
    show vsF p (vsLin p (p - ci) 0 r r) i = _
    rw [vsF_vsLin _ _ _ le_rfl]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_zero, zero_mul, add_zero]
    rw [hpc]
  refine ⟨vsLin_lt hp.pos _ _, by show (vsLin p (p - ci) 0 r r).length = _; rw [vsLin_length, hrl], ?_⟩
  simp only [hla, mul_smul]
  rw [← Finset.smul_sum]
  have e : ∑ i : Fin vs.length, vsF p r i • vsWV p d vs[i] = -(vsF p r vs.length • vsWV p d u) :=
    eq_neg_of_add_eq_zero_left hker
  rw [e, smul_neg, neg_smul, neg_neg, smul_smul, hrm', hinv, one_smul]

end

end GI.Proved
