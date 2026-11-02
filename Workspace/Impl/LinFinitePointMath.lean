import Workspace.Impl.LinFiniteAction
import Workspace.Impl.LinFiniteReduce

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linFinitePointVal {d : ℕ} (m : Fin d → ℕ) (x : linFiniteVec m) : Val :=
  linVecVal (linExtend (fun i => ((x i).val : ℤ)) 1)

/-- Apply the full matrix to the full point and reduce only the finite rows.
The final scalar is left unchanged by its modulus zero. -/
theorem linFiniteHomogeneous_apply {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (f : linFiniteVec m →+ linFiniteVec m) (u x : linFiniteVec m) :
    (fun i => (linFiniteHomogeneous m f u).mulVec
      (linExtend (fun k => ((x k).val : ℤ)) 1) i % linFiniteModuli m i) =
      linExtend (fun i => (((f x + u) i).val : ℤ)) 1 := by
  rw [linFiniteHomogeneous, linAffineMatrix_mulVec, one_smul]
  funext i
  induction i using Fin.lastCases with
  | last => simp [linFiniteModuli]
  | cast i =>
    simp only [linFiniteModuli, linExtend_castSucc, Pi.add_apply]
    exact linFiniteIntOffset_comp_mod m hm f u x i

/-- The full homogeneous point always has scalar one before reduction too. -/
theorem linFiniteHomogeneous_last {d : ℕ} (m : Fin d → ℕ)
    (f : linFiniteVec m →+ linFiniteVec m) (u x : linFiniteVec m) :
    (linFiniteHomogeneous m f u).mulVec (linExtend (fun k => ((x k).val : ℤ)) 1) (Fin.last d) = 1 := by
  rw [linFiniteHomogeneous, linAffineMatrix_mulVec]
  exact linExtend_last _ _

/-- A separate point-size bound prevents repeated layer updates from
compounding polynomial output bounds. -/
theorem linFinitePointVal_wt {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (x : linFiniteVec m) :
    (linFinitePointVal m x).wt ≤ 1000 * ((linVecVal (linFiniteModuli m)).wt + 1) ^ 2 := by
  let W := (linVecVal (linFiniteModuli m)).wt
  have hn : d + 1 ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (d + 1)).map fun i => encInt (linFiniteModuli m i))
    simp only [List.length_map, List.length_finRange] at hh
    exact hh.le
  have hentry (i : Fin (d + 1)) : (encInt (linExtend (fun k => ((x k).val : ℤ)) 1 i)).wt ≤ 100 * (W + 1) := by
    induction i using Fin.lastCases with
    | last =>
      simp only [linExtend_last]
      have hh : (encInt 1).wt ≤ 100 := by decide
      omega
    | cast i =>
      rw [linExtend_castSucc]
      haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
      have hw := linVecEntryWt (linFiniteModuli m) i.castSucc
      simp only [linFiniteModuli, linExtend_castSucc] at hw
      have hh := linFiniteRemainderWt ((x i).val : ℤ) (m i) W (hm i) hw.le
      have hx : (((x i).val : ℤ) % (m i : ℤ)) = ((x i).val : ℤ) := by
        apply Int.emod_eq_of_lt (by omega)
        have := ZMod.val_lt (x i)
        omega
      rw [hx] at hh
      exact hh.trans (by omega)
  have hh := linWtList (vs := (List.finRange (d + 1)).map fun i => encInt (linExtend (fun k => ((x k).val : ℤ)) 1 i))
    (B := 100 * (W + 1)) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact hentry i)
  simp only [List.length_map, List.length_finRange] at hh
  change (linFinitePointVal m x).wt ≤ _ at hh
  change (linFinitePointVal m x).wt ≤ 1000 * (W + 1) ^ 2
  nlinarith [Nat.mul_le_mul_right (100 * (W + 1)) hn]

end GI.Impl
