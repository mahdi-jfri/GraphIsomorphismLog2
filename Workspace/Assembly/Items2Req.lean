module

public import Workspace.Assembly.ItemsReq
public import Workspace.Impl.FinLayoutC23OK
public import Workspace.Impl.TermGlueLabPFin

@[expose] public section

/-!
# Stage 2 with concrete item dispatch and label dispatch

`final_modulo_items2` fills Case 2a init, the fixed programs of Cases 2b/3,
and the label dispatch. The remaining contracts describe the object stage,
the pair branch, the nonempty label program, the A.20 glue and the J program.
Binary refinement is installed at primitive 20.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- Stage 2 from the remaining program contracts and cited tasks. -/
theorem final_modulo_items2 (hst : PointwiseStab)
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
    (cfObF cfPrF rpF : List Expr) (hobF : cfObF.length ≤ 99000)
    (hprF : cfPrF.length ≤ 100000) (hrp : rpF.length ≤ fitRoom - fitRpOff)
    {K D Kj Dj Kg Dg Co Do : ℕ} (Xp : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F cfObF cfPrF) rpF)) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hne : Iface.TmGLPNeSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F cfObF cfPrF) rpF)) K D (flcLabIdx + 1))
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F cfObF cfPrF) rpF)) Kj Dj flcJIdx)
    (hobj : ItCfObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F cfObF cfPrF) rpF))
      (fitC23Idx + 1000) (fitC23Idx + 1001) (fitC23Idx + 1002) Co Do)
    (hpair : ItciPairSpec (fagIface hst hm hpre hfac hmb hO hC hder hni hnc (3 * K + 100) (D + 1)
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 Co Do Xp))))
      (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F cfObF cfPrF) rpF)) asmF (fitC23Idx + 100000) (fitC23Idx + 100001) (fitC23Idx + 100002) Xp)
    (hXp : PBU fun _ W _ => Xp W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hlF := tmGLPLabF_fits hneF
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF neF) jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  have hfit : FitFits itHvHvIF (fc23F cfObF cfPrF) rpF :=
    ⟨itHvHvIF_fits, fc23_fits hobF hprF, hrp⟩
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; decide
  have hlab := @flc_labSpec_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hF K D @hne
  have hinit := fit_hvInitOK_final (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (hs := hs) (hh := hh) (hn := hn) (hcmb := hcmb) (hv := hv)
    (ext'' := karyRefinementPrim h2 :: ext''') hk hF (crE := fcrE) (cmE := fcmE) ⟨fcr_fits, fcm_fits⟩ hfit
  obtain ⟨_, _, _, _, _, _, _, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
    hF (crE := fcrE) (cmE := fcmE) (itE := fitE)
    (itF := fitF itHvHvIF (fc23F cfObF cfPrF) rpF) ⟨fcr_fits, fcm_fits⟩
  obtain ⟨hA, _, hc23, _⟩ := fit_hasAt_parts hfit hit
  have hj : (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
      (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF neF) jF fcrE fcmE fitE fcrF fcmF
      (fitF itHvHvIF (fc23F cfObF cfPrF) rpF)).prims[20]? = some (karyRefinementPrim h2) := rfl
  have h23 := fc23_caseOK_final _ hobF hc23 hA h2 hj hobj hpair
  exact final_modulo_items hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl hk (karyRefinementPrim h2 :: ext''')
    gObjF (tmGLPLabF neF) jF hgo hlF hjF itHvHvIF (fc23F cfObF cfPrF) rpF
    itHvHvIF_fits (fc23_fits hobF hprF) hrp (itHvXh hfac hst) (fc23X h2 Co Do Xp)
    hgl hlab hjj (hinit _) (itHvXh_pbu hfac hst) h23 (fc23_X_pbu h2 Co Do hXp)

end GI.Assembly
