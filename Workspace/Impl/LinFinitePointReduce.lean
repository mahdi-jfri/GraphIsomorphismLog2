import Workspace.Impl.LinFinitePointMath

namespace GI.Impl
open GI.Cited GI.Lang

def linFinitePointReduceCost (W n : ℕ) : ℕ := linVectorBinaryCost W n (100 * (W + 1))

/-- The signed remainder program also handles the homogeneous scalar row:
its modulus is zero and its value is one. -/
theorem linFinitePointReduce_spec {P : Program} {b d : ℕ}
    (hp : P.HasAt b (linFiniteReduceFuns b)) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (x : Fin (d + 1) → ℤ) (hx : x (Fin.last d) = 1) :
    FunDet P b (.list [linVecVal x, linVecVal (linFiniteModuli m)])
      (linVecVal (fun i => x i % linFiniteModuli m i))
      (linFinitePointReduceCost (Val.list [linVecVal x, linVecVal (linFiniteModuli m)]).wt (d + 1)) := by
  let a := Val.list [linVecVal x, linVecVal (linFiniteModuli m)]
  let W := a.wt
  have hs := linInt_spec (hp.block 3 rfl)
  have wmod : (linVecVal (linFiniteModuli m)).wt < W := wt_le_wt_list (by simp [W, a])
  have hB (i : Fin (d + 1)) : (encInt (x i % linFiniteModuli m i)).wt ≤ 100 * (W + 1) := by
    induction i using Fin.lastCases with
    | last =>
      simp only [linFiniteModuli, linExtend_last, Int.emod_zero, hx]
      have h1 : (encInt 1).wt ≤ 100 := by decide
      omega
    | cast i =>
      simp only [linFiniteModuli, linExtend_castSucc]
      have hw := linVecEntryWt (linFiniteModuli m) i.castSucc
      simp only [linFiniteModuli, linExtend_castSucc] at hw
      have hh := linFiniteRemainderWt (x i.castSucc) (m i) W (hm i) (hw.le.trans wmod.le)
      omega
  exact linVectorBinary_spec (hp.block 0 rfl) (· % ·) hs.rem x (linFiniteModuli m) _ hB

theorem linFinitePointReduceCost_mono {W V n k : ℕ} (hW : W ≤ V) (hn : n ≤ k) :
    linFinitePointReduceCost W n ≤ linFinitePointReduceCost V k := by
  simp only [linFinitePointReduceCost, linVectorBinaryCost, linVectorAccWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  gcongr

theorem linFinitePointReduceCost_poly : PBU (fun n W _ => linFinitePointReduceCost W n) := by
  simp only [linFinitePointReduceCost, linVectorBinaryCost, linVectorAccWt,
    linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

end GI.Impl
