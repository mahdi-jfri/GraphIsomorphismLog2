module

public import Workspace.Assembly.Items4Req
public import Workspace.Impl.FinLayoutPr

@[expose] public section

/-!
# Stage 2 with the concrete pair room

`final_modulo_items5` is `final_modulo_items4` with the pair part made concrete,
`cfPrF := fc10PrF sojF` (`FinLayoutPr.lean`). The room holds a trampoline to the init of
`sojItem`, the pair start `itciPS` and step `itciPK`, the configuration branch with its library
blocks, and the sub-list `sojF` of `sojItem` at offset 1000. The pair contract `ItciPairSpec` is
`fc10_pairSpec`: the configuration branch is `itcq_cfgSpec_of`, and the two branches are joined
by `itci_pairSpec_of`. What remains of the pair part is the contract `ItciSojSpec` of `sojF`, at
the indices `fitC23Idx + 101000`, `+ 101001`, `+ 101002`, with a polynomial bound `Xs`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- Stage 2 from the remaining program contracts and cited tasks. -/
theorem final_modulo_items5 (hst : PointwiseStab)
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
    (gObjF neF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hneF : neF.length + 1 ≤ flcJOff - flcLabOff)
    (sojF : List Expr) (hsojF : sojF.length ≤ 99000)
    {K D Kg Dg : ℕ} (Xs : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hne : Iface.TmGLPNeSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) K D (flcLabIdx + 1))
    (hsoj : ∀ Kj Dj : ℕ, ItciSojSpec (fagIface hst hm hpre hfac hmb hO hC hder hni hnc (3 * K + 100) (D + 1)
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm)
          (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 (itCfObjCo hst) (itCfObjDo hst) (fc10Xp Xs)))))
      (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) asmF (fitC23Idx + 101000) (fitC23Idx + 101001) (fitC23Idx + 101002) Xs)
    (hXs : PBU fun _ W _ => Xs W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hprF := fc10PrF_fits hsojF
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF neF) tmJFinF :=
    ⟨tmRi_recF_fits hgo, tmGLPLabF_fits hneF, tmJFinF_fits⟩
  have hfit : FitFits itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx) :=
    rcR_fits itHvHvIF_fits (fc23_fits fc23ObF_length hprF)
  obtain ⟨_, _, _, _, _, _, _, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
    hF (crE := fcrE) (cmE := fcmE) (itE := fitE)
    (itF := fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx)) ⟨fcr_fits, fcm_fits⟩
  obtain ⟨_, _, hc23, _⟩ := fit_hasAt_parts hfit hit
  have hpr := (fc23_parts fc23ObF_length hc23).2.2
  exact final_modulo_items4 hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl hk h2 ext''' gObjF neF hgo hneF
    (fc10PrF sojF) hprF (fc10Xp Xs) hgl hne
    (fun Kj Dj => fc10_pairSpec _ hpr (hsoj Kj Dj)) (fc10Xp_pbu hXs)

end GI.Assembly
