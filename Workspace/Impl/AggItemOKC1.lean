import Workspace.Impl.AggItemStepC1
import Workspace.Impl.AggItemOK

/-!
# The bound of the Case 1 contract is polynomial

`itS_c1_caseOK` (`AggItemStepC1.lean`) gives the contract of Case 1 with the bound `itSC1X`.
This bound is polynomial (`itS_sc1X_pbu`), so it can serve as (part of) the common bound `Xc`
of `itS_asItemsOK`, through `ItSCaseOK.mono`.
-/

namespace GI.Impl

open GI.Lang

theorem itS_sc1X_pbu : PBU fun _ W _ => itSC1X W := by
  simp only [itSC1X, itSC1C, itSC1B, itSVB, cmOutB, cmPb, cmNb]
  norm_poly

end GI.Impl
