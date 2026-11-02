import Workspace.Assembly.CertReq
import Workspace.Impl.FinLayoutCmp

/-!
# Stage 2 with the comparison phase in place

`final_modulo_cert` left the comparison phase of the aggregation round open: an entry `cmE` at
`asb 3`, a helper list `cmF` at `fagCmIdx`, a bound `Xm`, the contract `AsCompOK` and the growth
`PBU` of `Xm`. Here we fill it with the comparison program (`FinLayoutCmp.lean`):
`cmE := fcmE`, `cmF := fcmF`, `Xm := cmRunX hst hpre hm`. The contract is `fag_asCompOK`, which
holds for every interface, so in particular for the one of `final_modulo_cert`, whose bound
contains `Xm` itself. The growth is `cm_runX_pbu`, and the room of `cmF` is `fcm_fits`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer)

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23 and the items.** T2, T4, the coset program T4–T6, the A.20 recursion, the reading,
the certificate phase and the comparison phase of the round are programs. -/
theorem final_modulo_cmp (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
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
    {Kl Dl Kj Dj Kg Dg : ℕ} (itE : Expr) (itF : List Expr) (Xi : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      fcmE itE fcrF fcmF itF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      fcmE itE fcrF fcmF itF) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE fcmE
      itE fcrF fcmF itF) Kj Dj flcJIdx)
    (hi : AsItemsOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) Xi))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ ext') (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE fcmE
        itE fcrF fcmF itF) asmF asHandImpl Xi (asb 4))
    (hXi : PBU fun _ W _ => Xi W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  -- The room of the coset slot, as in `final_modulo_glue`; it is needed by `fag_hasAt`.
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  exact final_modulo_cert hcite hst hm hpre hfac hmb hO hC hAb hOut hTr hcs hder hqc hni hsy hsc
    hnc hs hh hn hcmb hv dixon hK h6 hDl ext' gObjF labF jF hgo hlF hjF fcmE itE fcmF itF
    fcm_fits (cmRunX hst hpre hm) Xi hgl hlab hjj
    -- the comparison phase, for the interface of `final_modulo_cert` (`fag_asCompOK`)
    (fag_asCompOK _ hF fcr_fits) hi (cm_runX_pbu hst hpre hm) hXi

end GI.Assembly
