module

public import Workspace.Assembly.Items2Req
public import Workspace.Impl.FinLayoutObjFin
public import Workspace.Impl.AggRectRepFit

@[expose] public section

/-!
# Stage 2 with the concrete object stage and representation program

`final_modulo_items3` is `final_modulo_items2` with two more lists made concrete:
* the object stage of Cases 2b/3, `cfObF := fc23ObF` (`FinLayoutObjFin.lean`), whose contract
  `ItCfObjSpec` is now proved (`fc8_objSpec_final`), with constant `itCfObjCo hst` and exponent
  `itCfObjDo hst`;
* the representation program, `rpF := rcRepF fitRpIdx` (`AggRectRepFit.lean`).

The remaining contracts describe the pair branch, the nonempty label program, the A.20 glue and
the J program.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- Stage 2 from the remaining program contracts and cited tasks. -/
theorem final_modulo_items3 (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2) (ext''' : List Prim)
    (gObjF neF jF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hneF : neF.length + 1 ≤ flcJOff - flcLabOff) (hjF : jF.length ≤ flSupOff - flcJOff)
    (cfPrF : List Expr) (hprF : cfPrF.length ≤ 100000)
    {K D Kj Dj Kg Dg : ℕ} (Xp : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hne : Iface.TmGLPNeSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) K D (flcLabIdx + 1))
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) Kj Dj flcJIdx)
    (hpair : ItciPairSpec (fagIface hst hm hpre hfac hmb hO hC hder hni hnc (3 * K + 100) (D + 1)
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm)
          (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 (itCfObjCo hst) (itCfObjDo hst) Xp))))
      (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) asmF (fitC23Idx + 100000) (fitC23Idx + 100001) (fitC23Idx + 100002) Xp)
    (hXp : PBU fun _ W _ => Xp W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF neF) jF :=
    ⟨tmRi_recF_fits hgo, tmGLPLabF_fits hneF, hjF⟩
  have hfit : FitFits itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx) :=
    rcR_fits itHvHvIF_fits (fc23_fits fc23ObF_length hprF)
  obtain ⟨_, _, _, _, _, _, _, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
    hF (crE := fcrE) (cmE := fcmE) (itE := fitE)
    (itF := fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx)) ⟨fcr_fits, fcm_fits⟩
  obtain ⟨_, _, hc23, _⟩ := fit_hasAt_parts hfit hit
  have hobj := fc8_objSpec_final hst hc23 fcr_prim_pst
  exact final_modulo_items2 hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl hk h2 ext''' gObjF neF jF hgo hneF hjF
    fc23ObF cfPrF (rcRepF fitRpIdx) fc23ObF_length hprF hfit.hrp Xp hgl hne hjj hobj hpair hXp

end GI.Assembly
