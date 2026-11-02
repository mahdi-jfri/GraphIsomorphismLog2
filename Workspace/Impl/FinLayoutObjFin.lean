import Workspace.Impl.FinLayoutObj
import Workspace.Impl.FinLayoutC23OK

/-! # The object stage in its final slot

The object room of the Case 2b/3 list starts at `fitC23Idx + 1000` (`fc23F`). `fc23ObF` is the
object-stage list `fc8ObConc` for that base. It has 214 functions, so it fits the room of
99000 functions, and the col, orbital and design entries sit at `fitC23Idx + 1000`, `+ 1001`
and `+ 1002`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (PointwiseStab)

/-- The object-stage list installed at `fitC23Idx + 1000`. -/
def fc23ObF : List Expr := fc8ObConc (fitC23Idx + 1000)

theorem fc23ObF_length : fc23ObF.length ≤ 99000 := by
  rw [fc23ObF, fc8_obConc_length]; decide

/-- **The object stage of the final Case 2b/3 list** meets `ItCfObjSpec`. -/
theorem fc8_objSpec_final (hps : PointwiseStab) {P : Program} {cfPrF : List Expr}
    (h : P.HasAt fitC23Idx (fc23F fc23ObF cfPrF))
    (hj : P.prims[0]? = some (pointwiseStabPrim hps)) :
    ItCfObjSpec P (fitC23Idx + 1000) (fitC23Idx + 1001) (fitC23Idx + 1002)
      (itCfObjCo hps) (itCfObjDo hps) :=
  fc8_objSpec hps (fc23_parts fc23ObF_length h).2.1 hj

end GI.Impl
