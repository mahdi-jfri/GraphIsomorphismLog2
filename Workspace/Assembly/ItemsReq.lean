import Workspace.Assembly.CmpReqK
import Workspace.Impl.FinLayoutItemsOK

/-!
# Stage 2 with the items in place

`final_modulo_cmp_k` left the items of the aggregation round open: an entry `itE` at `asb 4`,
a list `itF` at `fagItIdx`, a bound `Xi`, the contract `AsItemsOK` and the growth `PBU` of `Xi`.
Here we fill them with the layout of `FinLayoutItemsOK.lean`: `itE := fitE`,
`itF := fitF hvIF c23F rpF` and `Xi := fitXi hk hst hO Xh X3`. The programs of the items that
are written (the structure step, the run, Case 1, the branch step of Case 2a, the certificate
search) are fixed. Three lists are not written yet, and stay parameters with their room:

* `hvIF` at `fitHvIdx`: the init program of Case 2a, with its contract `ItHvInitOK` and bound
  `Xh`;
* `c23F` at `fitC23Idx`: the programs of Cases 2b and 3 (init at `fitC23Idx`, branch step at
  `fitC23Idx + 1`), with their contract `ItSCaseOK` and bound `X3`;
* `rpF` at `fitRpIdx`: the rectangle representation program. Its contract `RcRepSpec` is not a
  hypothesis here: only the programs of Cases 2b and 3 call it, so the proof of their `ItSCaseOK` takes
  `RcRepSpec … fitRpIdx …` as a hypothesis, together with
  `fit_rcCertSpec_final` for the certificate search at `fitRcIdx`.

The contract `AsItemsOK` is `fit_asItemsOK`, which holds for every interface. The growth of the
bound is `fit_Xi_pbu`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23, the init program of Case 2a, the programs of Cases 2b and 3, and the rectangle
representation program.** T2, T4, the coset program T4–T6, the A.20 recursion, the reading, the
certificate phase, the comparison phase, the structure step and the run of the items, Case 1, the
branch step of Case 2a and the certificate search are programs. -/
theorem final_modulo_items (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hsc : SylowConjugate)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDl : GI.Cited.DesignLemma) (hk : KaryRefinement P₀.κ) (ext'' : List Prim)
    (gObjF labF jF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hlF : labF.length ≤ flcJOff - flcLabOff) (hjF : jF.length ≤ flSupOff - flcJOff)
    (hvIF c23F rpF : List Expr) (hhv : hvIF.length ≤ fitC23Off - fitHvOff)
    (hc23 : c23F.length ≤ fitRpOff - fitC23Off) (hrp : rpF.length ≤ fitRoom - fitRpOff)
    {Kl Dl Kj Dj Kg Dg : ℕ} (Xh X3 : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kj Dj flcJIdx)
    (hinit : ItHvInitOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) (fitXi hk hst hO Xh X3)))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
        labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) asmF fitHvIdx Xh)
    (hXh : PBU fun _ W _ => Xh W)
    (h23 : ItSCaseOK (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc Kl Dl
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) (fitXi hk hst hO Xh X3)))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
        labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) asmF
      (fun a => a = .twoB ∨ a = .three) fitC23Idx (fitC23Idx + 1) X3)
    (hX3 : PBU fun _ W _ => X3 W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  -- the room of the coset slot and of the two phase lists, as in `final_modulo_cmp`
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  exact final_modulo_cmp_k hcite hst hm hpre hfac hmb hO hC hAb hOut hTr hcs hder hqc hni hsy hsc
    hnc hs hh hn hcmb hv dixon hK h6 hDl hk ext'' gObjF labF jF hgo hlF hjF fitE
    (fitF hvIF c23F rpF) (fitXi hk hst hO Xh X3) hgl hlab hjj
    -- the items, for the interface of `final_modulo_cmp_k` (`fit_asItemsOK`)
    (fit_asItemsOK hk hF ⟨fcr_fits, fcm_fits⟩ ⟨hhv, hc23, hrp⟩ _ hinit h23)
    (fit_Xi_pbu hk hst hO hXh hX3)

end GI.Assembly
