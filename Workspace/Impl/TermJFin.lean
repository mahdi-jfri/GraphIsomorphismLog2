module

public import Workspace.Impl.TermJLayAt
public import Workspace.Impl.FinLayoutAgg
public import Workspace.Impl.LinPrims

@[expose] public section

/-!
# The `J`-answer in the final program

`tmJFinF` is the code of the `J`-answer (`tmJFuns` at `flcJIdx`, 69 blocks of 1000). It fits
its room (`tmJFinF_fits`, the field `FlcFits.hjj`), and `tmJ_final` proves
`Iface.TermJSpec … tmJFinF … Kj Dj flcJIdx` for the final program `fagProg`, in the form that
`final_modulo_items2` takes as its hypothesis `hjj` (there `ext = linA20Extra … ++ ext'`).

The cited algorithms enter at their primitive indices: PointwiseStab `0`, Membership `1`,
NormalizedFactor `3`, GroupOrder `5`, NormalizedIntersection `10`, HermiteFullRank `15`,
ConstructiveMembership `17`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer)

/-- **The code of the `J`-answer** at `flcJIdx`. -/
def tmJFinF : List Expr := tmJFuns flcJIdx

theorem tmJFinF_fits : tmJFinF.length ≤ flSupOff - flcJOff := by
  rw [tmJFinF, length_tmJFuns]; unfold flSupOff flcJOff; norm_num

/-- **`TermJSpec` at `flcJIdx` in the final program.** -/
theorem tmJ_final (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (hO : GroupOrder) (hni : NormalizedIntersection) (hh : HermiteFullRank)
    (hcmb : ConstructiveMembership) :
    ∃ Kj Dj : ℕ, ∀ (hpre : Preimage) (hmb : MinimalBlocks) (hC : CameronRecognition)
      (hder : DerivedSubgroup)
      (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hn : SmithNonsingular)
      (hv : VectorStabilizer) (ext' : List Prim) (recF labF : List Expr) (crE cmE itE : Expr)
      (crF cmF itF : List Expr),
      recF.length ≤ flcLabOff - flcRecOff → labF.length ≤ flcJOff - flcLabOff →
      Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') recF labF tmJFinF crE cmE itE crF cmF itF)
        Kj Dj flcJIdx := by
  obtain ⟨K, D, hT⟩ := tmJ_termJSpec hm hfac hcmb hh hO hni hst
  refine ⟨K, D, fun hpre hmb hC hder hnc hs hn hv ext' recF labF crE cmE itE
    crF cmF itF hrec hlab => ?_⟩
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; decide
  have hF : FlcFits recF labF tmJFinF := ⟨hrec, hlab, tmJFinF_fits⟩
  have hJ := (flc_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (hmb := hmb)
    (hO := hO) (hC := hC) (hder := hder) (hni := hni)
    (hnc := hnc) (ext := linA20Extra hs hh hn hcmb hv ++ ext')
    (agg := fagAgg crE cmE itE crF cmF itF) hg hF).2.2.2
  obtain ⟨h0, hne, hHA⟩ := tmJLay_at hJ
  have h0' : _ = some (tmJTopF (tmJA flcJIdx 1)) := h0
  intro Ω C _
  exact hT (f := flcJIdx) h0' hne hHA rfl rfl rfl rfl rfl rfl rfl

end GI.Impl
