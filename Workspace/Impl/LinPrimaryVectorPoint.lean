module

public import Workspace.Impl.LinPrimaryVector

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryVector_point_spec {P : Program} {b p d : ℕ}
    (h : linPrimaryVectorAt P b) (hp : 0 < p) (ν : Fin d → ℕ) (level : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) :
    FunDet P b (.list [.nat p, .nat (p ^ level), linFinitePointVal (linPrimaryOrders p ν) x, encFun ν])
      (encVec (linPrimaryCoord p ν level x))
      (linPrimaryVectorCost (Val.list [.nat p, .nat (p ^ level), linFinitePointVal (linPrimaryOrders p ν) x, encFun ν]).wt d) := by
  let y := linExtend (fun i => (x i).val) 1
  have he : (fun i => (y i : ℤ)) = linExtend (fun i => ((x i).val : ℤ)) 1 := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [y]
    | cast i => simp [y]
  have ho : (fun i : Fin d => ((y i.castSucc / p ^ level : ℕ) : ZMod p)) = linPrimaryCoord p ν level x := by
    funext i
    simp [y, linPrimaryCoord]
  simpa only [he, ho, linFinitePointVal] using linPrimaryVector_spec h hp (p ^ level) y ν

end GI.Impl
