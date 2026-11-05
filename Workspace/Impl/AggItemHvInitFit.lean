module

public import Workspace.Impl.AggItemHvInitL
public import Workspace.Impl.FinLayoutItemsOK

@[expose] public section

/-!
# Case 2a: the init program in the final program

The list `hvIF` of `final_modulo_items` at `fitHvIdx` can be `itHvHvIF := itHvConc fitHvIdx
(fitC1Idx fagItIdx)`: the init program of Case 2a with all its functions, using the Case 1
helpers of `fitConc fagItIdx`. It fits its room (`itHvHvIF_fits`).

`fit_hvInitOK_final` proves the hypothesis `hinit` of `final_modulo_items` for this list and the
bound `itHvXh hfac hst`, for every interface `I`; `itHvXh_pbu` proves `hXh`. The cited tasks enter
only as the primitives **NormalizedFactor** (`3`) and **PointwiseStab** (`0`) of the final program.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Cited

/-- **The Case 1 helpers** of `fitConc c` form an `ItC1Ok` table at `fitC1Idx c`. -/
theorem fit_c1Ok {P : Program} {c : ℕ} (hA : FitAt P c) : ItC1Ok P (fitC1Idx c) :=
  ⟨hA.c1, hA.rb, hA.dat, hA.mpS, hA.sz, hA.cnt, hA.mpP, hA.pb, hA.flt, hA.kb, hA.inv, hA.chk,
    hA.al, hA.ct, hA.fnd, hA.ft, hA.swt, hA.sb, hA.gen, hA.mpT, hA.trB, hA.mpG, hA.gb, hA.bs,
    hA.bb, hA.app, hA.sch, hA.mpS2, hA.sb2, hA.cmp, hA.par, hA.mpI, hA.ib, hA.fltI, hA.it,
    hA.fld, hA.st⟩

/-- The list of the init program of Case 2a in the final program. -/
noncomputable def itHvHvIF : List Expr := itHvConc fitHvIdx (fitC1Idx fagItIdx)

theorem itHvHvIF_fits : itHvHvIF.length ≤ fitC23Off - fitHvOff := by
  rw [itHvHvIF, length_itHvConc]; unfold fitC23Off fitHvOff; omega

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
  {hder : DerivedSubgroup} {hni : NormalizedIntersection}
  {hnc : NormalClosure}
  {hs : SolvableCosetIntersection} {hh : HermiteFullRank} {hn : SmithNonsingular}
  {hcmb : ConstructiveMembership} {hv : VectorStabilizer} {ext'' : List Prim}
  {recF labF jF : List Expr}

/-- **The init program of Case 2a in the final program meets `ItHvInitOK`** at `fitHvIdx`, with
the bound `itHvXh hfac hst`, for every interface `I`. -/
theorem fit_hvInitOK_final (hk : KaryRefinement P₀.κ) (hF : FlcFits recF labF jF)
    {crE cmE : Expr} {crF cmF : List Expr} (hA : FagFits crF cmF) {c23F rpF : List Expr}
    (hfit : FitFits itHvHvIF c23F rpF) (I : Iface) :
    ItHvInitOK I (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF itHvHvIF c23F rpF)) asmF fitHvIdx (itHvXh hfac hst) := by
  obtain ⟨-, -, -, -, -, -, -, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) hF (crE := crE) (cmE := cmE)
    (itE := fitE) (itF := fitF itHvHvIF c23F rpF) hA
  obtain ⟨hC', hhv, -, -⟩ := fit_hasAt_parts hfit hit
  exact it_hvConc_initOK I hfac hst (fit_c1Ok hC') hhv rfl rfl

end Asm

end GI.Impl
