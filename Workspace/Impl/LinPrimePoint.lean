module

public import Workspace.Impl.LinPrimeAction
public import Workspace.Impl.LinFinitePointReduce

@[expose] public section

/-! Project a retained full point without changing its homogeneous scalar. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimePoint_reduce {d p : ℕ} {m : Fin d → ℕ}
    (D : linPrimeSplitData m p) (hm : ∀ i, 0 < m i) (x : linFiniteVec m) :
    (fun i => linExtend (fun i => ((x i).val : ℤ)) 1 i %
      linFiniteModuli (linPrimaryOrders p D.exponent) i) =
      linExtend (fun i => ((linPrimeProjection D x i).val : ℤ)) 1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [linFiniteModuli]
  | cast i => simpa [linFiniteModuli] using (linPrimeProjection_int D hm x i).symm

def linPrimePointFuns (b : ℕ) : List Expr := linFiniteReduceFuns b

theorem linPrimePointFuns_length (b : ℕ) : (linPrimePointFuns b).length = 21 := rfl

def linPrimePointCost (W : ℕ) : ℕ := linFinitePointReduceCost W W

set_option maxHeartbeats 1000000 in
theorem linPrimePoint_spec {P : Program} {b d p : ℕ} {m : Fin d → ℕ}
    (h : P.HasAt b (linPrimePointFuns b)) (D : linPrimeSplitData m p)
    (hp : p.Prime) (hm : ∀ i, 0 < m i) (x : linFiniteVec m) :
    let a := Val.list [linFinitePointVal m x,
      linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent))]
    FunDet P b a (linFinitePointVal (linPrimaryOrders p D.exponent) (linPrimeProjection D x))
      (linPrimePointCost a.wt) := by
  have hq : ∀ i, 0 < linPrimaryOrders p D.exponent i := fun i => pow_pos hp.pos _
  have hs := linFinitePointReduce_spec h (linPrimaryOrders p D.exponent) hq
    (linExtend (fun i => ((x i).val : ℤ)) 1) (by simp)
  rw [linPrimePoint_reduce D hm x] at hs
  have hd : d + 1 ≤ (Val.list [linFinitePointVal m x,
      linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent))]).wt := by
    have hl := length_lt_wt_list ((List.finRange (d + 1)).map
      (fun i => encInt (linFiniteModuli (linPrimaryOrders p D.exponent) i)))
    have hw := wt_le_wt_list (vs := [linFinitePointVal m x,
      linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent))])
      (v := linVecVal (linFiniteModuli (linPrimaryOrders p D.exponent))) (by simp)
    simp only [List.length_map, List.length_finRange] at hl
    exact hl.le.trans hw.le
  exact hs.mono (linFinitePointReduceCost_mono le_rfl hd)

theorem linPrimePointCost_poly : PBU (fun _ W _ => linPrimePointCost W) := by
  unfold linPrimePointCost linFinitePointReduceCost linVectorBinaryCost linVectorAccWt
    linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

end GI.Impl
