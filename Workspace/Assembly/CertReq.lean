module

public import Workspace.Assembly.GlueReq
public import Workspace.Impl.FinLayoutCert

@[expose] public section

/-!
# Stage 2 with the certificate phase in place

`final_modulo_glue` left the certificate phase of the aggregation round open: an entry `crE`
at `asb 2`, a helper list `crF` at `fagCrIdx`, a bound `Xc`, the contract `AsCertOK` and the
growth `PBU` of `Xc`. Here we fill it with the certificate program (`FinLayoutCert.lean`):
`crE := fcrE`, `crF := fcrF`, `Xc := cpCertX hst hpre hm`. The contract is `fag_asCertOK`, which
holds for every interface, so in particular for the one of `final_modulo_glue`, whose bound
contains `Xc` itself. The growth is `cpCertX_pbu`. The room of `crF` is `fcr_fits`, so `FagFits`
reduces to the room of `cmF`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer)

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23, the comparison phase and the items.** T2, T4, the coset program T4–T6, the A.20
recursion, the reading and the certificate phase of the round are programs. -/
theorem final_modulo_cert (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) (ext' : List Prim)
    (gObjF labF jF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hlF : labF.length ≤ flcJOff - flcLabOff) (hjF : jF.length ≤ flSupOff - flcJOff)
    {Kl Dl Kj Dj Kg Dg : ℕ}
    (cmE itE : Expr) (cmF itF : List Expr) (hcmF : cmF.length ≤ fagItOff - fagCmOff)
    (Xm Xi : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      cmE itE fcrF cmF itF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      cmE itE fcrF cmF itF) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE cmE
      itE fcrF cmF itF) Kj Dj flcJIdx)
    (hcm : AsCompOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE cmE
        itE fcrF cmF itF) asmF asHandImpl Xm (asb 3))
    (hi : AsItemsOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE cmE
        itE fcrF cmF itF) asmF asHandImpl Xi (asb 4))
    (hXm : PBU fun _ W _ => Xm W) (hXi : PBU fun _ W _ => Xi W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  -- The room of the coset slot, as in `final_modulo_glue`; it is needed by `fag_hasAt`.
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  exact final_modulo_glue hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl ext' gObjF labF jF hgo hlF hjF fcrE cmE itE fcrF cmF itF
    ⟨fcr_fits, hcmF⟩ (cpCertX hst hpre hm) Xm Xi hgl hlab hjj
    -- the certificate phase, for the interface of `final_modulo_glue` (`fag_asCertOK`)
    (fag_asCertOK _ hF hcmF) hcm hi
    (cpCertX_pbu hst hpre hm) hXm hXi

end GI.Assembly
