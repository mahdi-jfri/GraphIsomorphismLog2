import Workspace.Impl.LinFiniteAction

/-! Uniform bit-weight bounds on every full affine transformation, regardless
of the size of the cover group or the length of the word representing it. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linFiniteScalarBudget (W : ℕ) : ℕ := 20 * (W + 1) + 100
def linFiniteActionMatrixWeight (W d : ℕ) : ℕ :=
  linVectorAccWt (d + 1) (linVectorAccWt (d + 1) (linFiniteScalarBudget W))
def linFiniteActionWeight (W d : ℕ) : ℕ := 100 * (W + linFiniteActionMatrixWeight W d + 1)

theorem linFiniteCoordinateWt {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (x : linFiniteVec m) (i : Fin d) :
    (encInt ((x i).val : ℤ)).wt ≤ 20 * ((linVecVal (fun j => (m j : ℤ))).wt + 1) := by
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  apply linWtInt
  have hh := linEncIntAbs (m i : ℤ)
  have hw := linVecEntryWt (fun j => (m j : ℤ)) i
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw.le
  simp only [Int.natAbs_natCast] at hh ⊢
  exact (ZMod.val_lt (x i)).trans (hh.trans_le hp)

theorem linFiniteHomogeneous_wt {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (u : linFiniteVec m) :
    (encIntMatrix (linFiniteHomogeneous m f u)).wt ≤
      linFiniteActionMatrixWeight (linVecVal (fun j => (m j : ℤ))).wt d := by
  let W := (linVecVal (fun j => (m j : ℤ))).wt
  have he (i j : Fin (d + 1)) : (encInt (linFiniteHomogeneous m f u i j)).wt ≤ linFiniteScalarBudget W := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        have hh : (encInt 1).wt ≤ 100 := by decide
        simpa [linFiniteHomogeneous, linAffineMatrix, linFiniteScalarBudget] using hh.trans
          (show 100 ≤ linFiniteScalarBudget W by unfold linFiniteScalarBudget; omega)
      | cast j =>
        have hh : (encInt 0).wt ≤ 100 := by decide
        simpa [linFiniteHomogeneous, linAffineMatrix] using hh.trans
          (show 100 ≤ linFiniteScalarBudget W by unfold linFiniteScalarBudget; omega)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have hh := linFiniteCoordinateWt m hm u i
        simpa [linFiniteHomogeneous, linAffineMatrix] using hh.trans
          (show 20 * (W + 1) ≤ linFiniteScalarBudget W by unfold linFiniteScalarBudget; omega)
      | cast j =>
        have hh := linFiniteCoordinateWt m hm (f (linFiniteBasis m j)) i
        simpa [linFiniteHomogeneous, linAffineMatrix, linFiniteIntMatrix, linFiniteMatrix] using hh.trans
          (show 20 * (W + 1) ≤ linFiniteScalarBudget W by unfold linFiniteScalarBudget; omega)
  have hrow (i : Fin (d + 1)) : (linVecVal (linFiniteHomogeneous m f u i)).wt ≤
      linVectorAccWt (d + 1) (linFiniteScalarBudget W) := by
    have hh := linWtList (vs := (List.finRange (d + 1)).map fun j => encInt (linFiniteHomogeneous m f u i j))
      (B := linFiniteScalarBudget W) (by
        intro v hv; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv; exact he i j)
    simpa only [List.length_map, List.length_finRange, linVectorAccWt] using hh
  have hh := linWtList (vs := (List.finRange (d + 1)).map fun i => linVecVal (linFiniteHomogeneous m f u i))
    (B := linVectorAccWt (d + 1) (linFiniteScalarBudget W)) (by
      intro v hv; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv; exact hrow i)
  simpa only [List.length_map, List.length_finRange, linFiniteActionMatrixWeight, linVectorAccWt] using hh

theorem linFiniteModuli_wt {d : ℕ} (m : Fin d → ℕ) :
    (linVecVal (linFiniteModuli m)).wt ≤ (linVecVal (fun i => (m i : ℤ))).wt + 100 := by
  have he := linExtend_value encInt (fun i => (m i : ℤ)) 0
  have hh := wt_list_snoc_le ((List.finRange d).map fun i => encInt (m i : ℤ)) (encInt 0)
  have h0 : (encInt 0).wt ≤ 40 := by decide
  change (Val.list ((List.finRange (d + 1)).map fun i => encInt (linFiniteModuli m i))).wt ≤ _
  unfold linFiniteModuli
  rw [he]
  dsimp only [linVecVal] at *
  omega

theorem linFiniteAffineVal_wt {G : Type*} [Group G] {d : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : G → linFiniteVec m) (g : G) :
    (linFiniteAffineVal m ρ c g).wt ≤ linFiniteActionWeight (linVecVal (fun i => (m i : ℤ))).wt d := by
  have wp : 2 ≤ (linVecVal (fun i => (m i : ℤ))).wt :=
    (linVecVal (fun i => (m i : ℤ))).two_le_size.trans (linVecVal (fun i => (m i : ℤ))).size_le_wt
  have hM := linFiniteModuli_wt m
  have hA := linFiniteHomogeneous_wt m hm (linFiniteActionLinear m ρ g) (c g)
  have hI := linFiniteHomogeneous_wt m hm (linFiniteActionLinear m ρ g⁻¹) (c g⁻¹)
  have hh := wt_list3_le (linVecVal (linFiniteModuli m)) (encIntMatrix (linFiniteActionMatrix m ρ c g))
    (encIntMatrix (linFiniteActionMatrix m ρ c g⁻¹))
  change (Val.list _).wt ≤ _
  unfold linFiniteActionWeight
  dsimp only [linFiniteActionMatrix] at *
  omega

theorem linFiniteActionWeight_poly : PBU (fun d W _ => linFiniteActionWeight W d) := by
  unfold linFiniteActionWeight linFiniteActionMatrixWeight linFiniteScalarBudget linVectorAccWt
  norm_poly

end GI.Impl
