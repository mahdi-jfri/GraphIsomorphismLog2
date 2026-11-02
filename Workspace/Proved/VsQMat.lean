import Workspace.Proved.VsFMatPowMath
import Workspace.Impl.VsQTr
import Workspace.Cited.AlgoLinear

/-!
# Matrices over `𝔽_p` as lists

`vsQL M` is the list of rows of `M`, with entries `(M i j).val < p`; `vsQVec v` is the list of
entries of `v`. These are the canonical lists: a `d × d` list matrix with entries below `p`
is `vsQL` of the matrix it denotes (`vsQL_of_sq`). The input encoding `encModMatrix M` is the
list `vsQL M` (`encModMatrix_eq`).

* `vsQL_mul`: the product program on canonical lists gives the canonical list of the product.
* `vsQL_tr`: the transpose program gives the canonical list of the transpose.
-/

namespace GI.Proved

open GI.Impl GI.Lang GI.Cited Matrix

variable {p d : ℕ}

/-- The rows of a matrix, entries as numbers below `p`. -/
def vsQL (M : Matrix (Fin d) (Fin d) (ZMod p)) : List (List ℕ) :=
  (List.finRange d).map fun i => (List.finRange d).map fun j => (M i j).val

/-- The entries of a vector, as numbers below `p`. -/
def vsQVec (v : Fin d → ZMod p) : List ℕ := (List.finRange d).map fun j => (v j).val

theorem encVec_eq (v : Fin d → ZMod p) : encVec v = natList (vsQVec v) := by
  simp [encVec, vsQVec, natList, List.map_map, Function.comp_def]

theorem encModMatrix_eq (M : Matrix (Fin d) (Fin d) (ZMod p)) :
    encModMatrix M = .list ((vsQL M).map natList) := by
  simp only [encModMatrix, vsQL, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [encVec_eq, vsQVec]

theorem vsQVec_length (v : Fin d → ZMod p) : (vsQVec v).length = d := by simp [vsQVec]

theorem vsQVec_lt [NeZero p] (v : Fin d → ZMod p) : ∀ y ∈ vsQVec v, y < p := by
  intro y hy
  simp only [vsQVec, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact ZMod.val_lt _

theorem vsQL_sq [NeZero p] (M : Matrix (Fin d) (Fin d) (ZMod p)) : VsFSq p d (vsQL M) := by
  refine ⟨by simp [vsQL], fun a ha => ?_⟩
  simp only [vsQL, List.mem_map] at ha
  obtain ⟨i, -, rfl⟩ := ha
  refine ⟨fun y hy => ?_, by simp⟩
  simp only [List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact ZMod.val_lt _

theorem vsQL_getD (M : Matrix (Fin d) (Fin d) (ZMod p)) (i j : Fin d) :
    ((vsQL M).getD i []).getD j 0 = (M i j).val := by
  simp [vsQL, List.getD_eq_getElem?_getD]

theorem vsF_vsQVec [NeZero p] (v : Fin d → ZMod p) (j : Fin d) : vsF p (vsQVec v) j = v j := by
  simp [vsF, vsQVec, List.getD_eq_getElem?_getD]

theorem vsFMatrix_vsQL [NeZero p] (M : Matrix (Fin d) (Fin d) (ZMod p)) : vsFMatrix p d (vsQL M) = M := by
  ext i j
  simp only [vsFMatrix, vsF, vsQL_getD, ZMod.natCast_zmod_val]

/-- A canonical vector is determined by what it denotes. -/
theorem vsQVec_of [NeZero p] {x : List ℕ} (hl : x.length = d) (hx : ∀ y ∈ x, y < p) :
    x = vsQVec (fun j : Fin d => vsF p x j) := by
  apply List.ext_getElem (by simp [vsQVec, hl])
  intro k h1 h2
  simp only [vsQVec, List.getElem_map, List.getElem_finRange, vsF, Fin.cast_mk]
  rw [List.getD_eq_getElem _ _ h1, ZMod.val_natCast, Nat.mod_eq_of_lt (hx _ (List.getElem_mem _))]

/-- A canonical matrix is determined by what it denotes. -/
theorem vsQL_of_sq [NeZero p] {A : List (List ℕ)} (hA : VsFSq p d A) :
    A = vsQL (vsFMatrix p d A) := by
  apply List.ext_getElem (by simp [vsQL, hA.len])
  intro i h1 h2
  have hrow := hA.rows _ (List.getElem_mem h1)
  simp only [vsQL, List.getElem_map, List.getElem_finRange]
  have := vsQVec_of (p := p) hrow.2 hrow.1
  rw [this]
  simp only [vsQVec, vsFMatrix, vsF, Fin.cast_mk]
  congr 1
  funext j
  rw [List.getD_eq_getElem _ _ h1]

/-- **Products.** With a zero start vector of length `d`, the product program on canonical
lists gives the canonical list of the product. -/
theorem vsQL_mul [NeZero p] (A B : Matrix (Fin d) (Fin d) (ZMod p)) :
    vsFMatMulL p (vsQL A) (vsQL B) (List.replicate d 0) = vsQL (A * B) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hz : ∀ y ∈ List.replicate d 0, y < p := by
    intro y hy; rw [List.eq_of_mem_replicate hy]; exact hp
  have hsq := vsFMatMulL_sq hp (vsQL_sq A) (X := vsQL B) hz (by simp)
  rw [vsQL_of_sq hsq, vsFMatMulL_matrix (by simp [vsQL]) (vsQL_sq B) (by simp) (by
    funext j; simp [vsF, List.getD_eq_getElem?_getD]), vsFMatrix_vsQL, vsFMatrix_vsQL]

/-- **Transposes.** -/
theorem vsQL_tr (M : Matrix (Fin d) (Fin d) (ZMod p)) : vsQTr (vsQL M) d = vsQL Mᵀ := by
  apply List.ext_getElem (by simp [vsQTr, vsQL])
  intro i h1 h2
  simp only [vsQTr, List.getElem_map, List.getElem_range, vsQL, List.getElem_finRange]
  apply List.ext_getElem (by simp)
  intro j k1 k2
  simp only [List.getElem_map, List.getElem_finRange, transpose_apply]
  have hi : i < d := by simpa [vsQTr] using h1
  have hj : j < d := by simpa using k1
  simp only [Fin.cast_mk]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

end GI.Proved
