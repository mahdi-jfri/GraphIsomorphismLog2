module

public import Workspace.Impl.VsQChunk
public import Workspace.Proved.VsFAlgSpanMath
public import Workspace.Impl.VsBAct

@[expose] public section

/-!
# A combination of stored matrices

`vsBCombL p D c Lb` flattens the stored `D × D` matrices of `Lb`, takes the combination with
coefficients `c` (a row times a matrix), and cuts the result back into `D` rows.
`vsBComb_wM`: its matrix is `∑ c_k Lb_k`.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Lang

/-- The combination `∑ c_k Lb_k` of stored matrices. -/
def vsBCombL (p D : ℕ) (c : List ℕ) (Lb : List (List (List ℕ))) : List (List ℕ) :=
  vsQChunk 0 D D (vsFRowMul p c (Lb.map List.flatten) (List.replicate (D * D) 0))

variable {p : ℕ}

theorem vsBComb_sq (hp : 0 < p) (D : ℕ) (c : List ℕ) (Lb : List (List (List ℕ))) :
    VsWSq p D (vsBCombL p D c Lb) := by
  have hfit := vsFRowMul_fit (d := D * D) hp c (Lb.map List.flatten) _ (List.mem_singleton_self _)
  refine ⟨fun r hr => ⟨fun y hy => ?_, ?_⟩, by simp [vsBCombL, vsQChunk]⟩
  · simp only [vsBCombL, vsQChunk, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [List.getD_eq_getElem?_getD]
    cases h : (vsFRowMul p c (Lb.map List.flatten) (vsWZ (D * D)))[i * D + j]? with
    | none => simp [vsWZ] at h ⊢; simp [h]; exact hp
    | some y => 
      simp only [vsWZ] at h
      simp only [h, Option.getD_some]
      exact hfit.1 y (List.mem_of_getElem? h)
  · simp only [vsBCombL, vsQChunk, List.mem_map, List.mem_range] at hr
    obtain ⟨i, -, rfl⟩ := hr
    simp

theorem vsBComb_wM {D : ℕ} (c : List ℕ) {Lb : List (List (List ℕ))} (hLb : ∀ M ∈ Lb, VsWSq p D M) :
    vsWM p D (vsBCombL p D c Lb) =
      ∑ k ∈ Finset.range Lb.length, ((c.getD k 0 : ℕ) : ZMod p) • vsWM p D (Lb.getD k []) := by
  ext j i
  have hflat : ∀ r ∈ Lb.map List.flatten, r.length ≤ (List.replicate (D * D) 0).length := by
    intro r hr
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hr
    rw [List.length_replicate, vsFA_flatten_length (fun r hr => ((hLb M hM).1 r hr).2), (hLb M hM).2]
  have hrow := congrFun (vsFMat_rowMul p c (Lb.map List.flatten) (List.replicate (D * D) 0) hflat) (i * D + j)
  simp only [vsWM, transpose_apply, vsFMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hi : (i : ℕ) < D := i.2
  have hj : (j : ℕ) < D := j.2
  have hrowi : (vsBCombL p D c Lb).getD i [] = (List.range D).map fun j' =>
      (vsFRowMul p c (Lb.map List.flatten) (List.replicate (D * D) 0)).getD (i * D + j') 0 := by
    simp [vsBCombL, vsQChunk, List.getD_eq_getElem?_getD, hi]
  rw [hrowi, vsF_apply, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [← vsF_apply, hrow]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vsF_apply]
  have hz : ((List.replicate (D * D) 0).getD (↑i * D + ↑j) 0 : ℕ) = 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
  rw [hz, Nat.cast_zero, zero_add, List.length_map]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  have hk' := Finset.mem_range.mp hk
  have e1 : (Lb.map List.flatten).getD k [] = (Lb.getD k []).flatten := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, List.getD_eq_getElem _ _ hk']
  have hM : Lb.getD k [] ∈ Lb := by rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
  rw [e1, vsFA_flatten_getD (fun r hr => ((hLb _ hM).1 r hr).2) i j hj]

end GI.Proved
