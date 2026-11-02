import Workspace.Impl.AggRectRepT14
import Workspace.Impl.FinLayoutItemsOK

/-!
# The representation program in the final program

`rcR_fit_repSpec_final`: with `rpF := rcRepF fitRpIdx` in the items' list `fitF`, the
representation program at `fitRpIdx` meets `RcRepSpec` with the bound `rcRB hst hpre`
(polynomial by `rcRB_pbu`). PointwiseStab is primitive `0` and Preimage is primitive `2` of
the final program (`fcr_prim_pst`, `fag_prim_pre`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

set_option maxRecDepth 100000

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {hsy : SylowAlgo} {hsc : SylowConjugate} {hnc : NormalClosure}
  {hs : SolvableCosetIntersection} {hh : HermiteFullRank} {hn : SmithNonsingular}
  {hcmb : ConstructiveMembership} {hv : VectorStabilizer} {ext'' : List Prim}
  {recF labF jF : List Expr}

/-- The representation program fits its room. -/
theorem rcR_fits {hvIF c23F : List Expr} (hhv : hvIF.length ≤ fitC23Off - fitHvOff)
    (hc23 : c23F.length ≤ fitRpOff - fitC23Off) : FitFits hvIF c23F (rcRepF fitRpIdx) :=
  ⟨hhv, hc23, by rw [length_rcRepF]; unfold fitRoom fitRpOff; omega⟩

/-- **The representation program in the final program** meets `RcRepSpec` at `fitRpIdx`. -/
theorem rcR_fit_repSpec_final (hk : KaryRefinement P₀.κ) (hF : FlcFits recF labF jF)
    {crE cmE : Expr} {crF cmF : List Expr} (hA : FagFits crF cmF) {hvIF c23F : List Expr}
    (hhv : hvIF.length ≤ fitC23Off - fitHvOff) (hc23 : c23F.length ≤ fitRpOff - fitC23Off) :
    RcRepSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF hvIF c23F (rcRepF fitRpIdx))) fitRpIdx (rcRB hst hpre) := by
  obtain ⟨-, -, -, -, -, -, -, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc)
    (hni := hni) (hsy := hsy) (hsc := hsc) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) hF (crE := crE) (cmE := cmE)
    (itE := fitE) (itF := fitF hvIF c23F (rcRepF fitRpIdx)) hA
  exact rcR_repSpec_at (fit_hasAt_parts (rcR_fits hhv hc23) hit).2.2.2 hst rfl hpre rfl

end Asm

end GI.Impl
