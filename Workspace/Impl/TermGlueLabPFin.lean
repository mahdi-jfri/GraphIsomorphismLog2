import Workspace.Impl.TermGlueLabPTop
import Workspace.Impl.FinLayoutCos

/-!
# The label program at `flcLabIdx` in the final program

The label list is `tmGLPLabF neF = tmGLPTopF (flcLabIdx + 1) :: neF`: the dispatch
of `TermGlueLabPTop` at `flcLabIdx`, then the code `neF` of the nonempty part at
`flcLabIdx + 1`. `flc_labSpec_of_ne`: `TermGlueLabSpec` at `flcLabIdx` in the final program
from `TmGLPNeSpec` at `flcLabIdx + 1`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure)

/-- **The label list**: the dispatch at `flcLabIdx`, the nonempty part from `flcLabIdx + 1`. -/
def tmGLPLabF (neF : List Expr) : List Expr := tmGLPTopF (flcLabIdx + 1) :: neF

theorem length_tmGLPLabF (neF : List Expr) : (tmGLPLabF neF).length = neF.length + 1 := rfl

/-- The label list fits its room when the nonempty part has fewer than `249999` functions. -/
theorem tmGLPLabF_fits {neF : List Expr} (h : neF.length + 1 ≤ flcJOff - flcLabOff) :
    (tmGLPLabF neF).length ≤ flcJOff - flcLabOff := by
  rw [length_tmGLPLabF]; exact h

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {hsy : SylowAlgo} {hsc : SylowConjugate} {hnc : NormalClosure}
  {ext : List Prim} {gen agg recF neF jF : List Expr}

/-- The nonempty part sits at `flcLabIdx + 1` in the final program. -/
theorem flc_hasAt_ne (hg : gen.length ≤ asmSlot) (hF : FlcFits recF (tmGLPLabF neF) jF) :
    (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext gen recF
      (tmGLPLabF neF) jF agg).HasAt (flcLabIdx + 1) neF := by
  have h := (flc_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (hmb := hmb)
    (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc) (hni := hni) (hsy := hsy)
    (hsc := hsc) (hnc := hnc) (ext := ext) (agg := agg) hg hF).2.2.1
  have := h.right (A := [tmGLPTopF (flcLabIdx + 1)])
  simpa using this

/-- **`TermGlueLabSpec` at `flcLabIdx` in the final program**, from the contract of the
nonempty part at `flcLabIdx + 1`. -/
theorem flc_labSpec_of_ne (hg : gen.length ≤ asmSlot) (hF : FlcFits recF (tmGLPLabF neF) jF)
    {K D : ℕ}
    (hne : Iface.TmGLPNeSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      ext gen recF (tmGLPLabF neF) jF agg) K D (flcLabIdx + 1)) :
    Iface.TermGlueLabSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext
      gen recF (tmGLPLabF neF) jF agg) (3 * K + 100) (D + 1) flcLabIdx := by
  have h := (flc_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (hmb := hmb)
    (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc) (hni := hni) (hsy := hsy)
    (hsc := hsc) (hnc := hnc) (ext := ext) (agg := agg) hg hF).2.2.1
  have hf := (h.left (A := [tmGLPTopF (flcLabIdx + 1)]) (B := neF)).single
  exact @tmGLP_top_spec _ flcLabIdx (flcLabIdx + 1) K D hf @hne

end GI.Impl
