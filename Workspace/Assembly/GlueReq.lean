import Workspace.Assembly.AggPhReq
import Workspace.Impl.TermRecFin

/-!
# Stage 2 with the A.20 recursion in place

`final_modulo_aggph` left `TermRecSpec` at `flcRecIdx` open, for any list `recF` and any extra
primitives `ext`. It holds (`tmRi_flcRecSpec`) for

* `recF = tmRiRecF flcRecIdx 14 8 1 gObjF`, the recursion of Lemma A.20 with the glue program
  `gObjF` at `flcRecIdx + tmRiGlueOff`;
* `ext = linA20Extra hs hh hn hcmb hv ++ ext'`, so that the primitives `14`–`18` are
  SolvableCosetIntersection, HermiteFullRank, SmithNonsingular, ConstructiveMembership and
  VectorStabilizer, in the order of the primitive table;

from the glue spec `TermGlueObjSpec` at `flcRecIdx + tmRiGlueOff`. The recursion calls
SolvableCosetIntersection at `14`, DerivedSubgroup at `8` and Membership at `1`.

Here we plug that proof in. The constants of `TermRecSpec` that `tmRi_flcRecSpec` gives depend
only on the three cited tasks and on the constants `Kg Dg` of the glue spec. We name them
`fglRecK`, `fglRecD`. The phase contracts are stated for the interface with these constants.
The room of `recF` in `FlcFits` follows from a bound on `gObjF` (`tmRi_recF_fits`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer)

/-- The first constant of `TermRecSpec` that `tmRi_flcRecSpec` gives. -/
noncomputable def fglRecK (hs : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hm : Membership) (Kg Dg : ℕ) : ℕ :=
  (tmRi_flcRecSpec hs hder hm Kg Dg).choose

/-- The second constant of `TermRecSpec` that `tmRi_flcRecSpec` gives. -/
noncomputable def fglRecD (hs : SolvableCosetIntersection) (hder : DerivedSubgroup)
    (hm : Membership) (Kg Dg : ℕ) : ℕ :=
  (tmRi_flcRecSpec hs hder hm Kg Dg).choose_spec.choose

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23 and three phases of the aggregation round.** T2, T4, the coset program T4–T6, the
A.20 recursion and the reading of the round are programs. -/
theorem final_modulo_glue (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hsc : SylowConjugate)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDl : GI.Cited.DesignLemma) (ext' : List Prim)
    (gObjF labF jF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hlF : labF.length ≤ flcJOff - flcLabOff) (hjF : jF.length ≤ flSupOff - flcJOff)
    {Kl Dl Kj Dj Kg Dg : ℕ}
    (crE cmE itE : Expr) (crF cmF itF : List Expr) (hA : FagFits crF cmF)
    (Xc Xm Xi : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE
      cmE itE crF cmF itF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE
      cmE itE crF cmF itF) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE cmE
      itE crF cmF itF) Kj Dj flcJIdx)
    (hct : AsCertOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg) (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xc (asb 2))
    (hcm : AsCompOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg) (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xm (asb 3))
    (hi : AsItemsOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg) (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xi (asb 4))
    (hXc : PBU fun _ W _ => Xc W) (hXm : PBU fun _ W _ => Xm W) (hXi : PBU fun _ W _ => Xi W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  -- The room of the three lists; the one of `recF` comes from the bound on `gObjF`.
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  -- `TermRecSpec` at `flcRecIdx`, with the constants `fglRecK`, `fglRecD`, by `tmRi_flcRecSpec`.
  -- The generator list of `fagProg` is `gsGen`, which fits in its slot.
  have hrec : Iface.TermRecSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF crE
      cmE itE crF cmF itF) (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg) flcRecIdx :=
    (tmRi_flcRecSpec hs hder hm Kg Dg).choose_spec.choose_spec
      (hst := hst) (hpre := hpre) (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hcs := hcs)
      (hqc := hqc) (hni := hni) (hsy := hsy) (hsc := hsc) (hnc := hnc) (hh := hh) (hn := hn)
      (hcm := hcmb) (hv := hv) (ext' := ext') (gen := gsGen) (labF := labF) (jF := jF)
      (agg := fagAgg crE cmE itE crF cmF itF)
      (by rw [length_gsGen]; unfold asmSlot; omega) hF hgl
  exact final_modulo_aggph hcite hst hm hpre hfac hmb hO hC hAb hOut hTr hcs hder hqc hni hsy
    hsc hnc dixon hK h6 hDl (linA20Extra hs hh hn hcmb hv ++ ext')
    (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF hF (Kc := fglRecK hs hder hm Kg Dg)
    (Dc := fglRecD hs hder hm Kg Dg) crE cmE itE crF cmF itF hA Xc Xm Xi hrec hlab hjj hct hcm
    hi hXc hXm hXi

end GI.Assembly
