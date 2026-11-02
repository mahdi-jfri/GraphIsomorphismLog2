import Workspace.Assembly.Items5Req
import Workspace.Impl.TermGlueLabNConc

/-!
# Stage 2 with the concrete label program

`final_modulo_items6` is `final_modulo_items5` with the nonempty part of the label program made
concrete, `neF := tmGLNeConc (flcLabIdx + 1) flSupIdx` (`TermGlueLabNConc.lean`): the label
driver of Theorem A.23 with all its modules, calling T4 at `flSupIdx`. Its contract
`TmGLPNeSpec` is `tmGLN_conc_spec`, at the constants `items6K`, `items6D`. So the hypotheses
`hneF` (the room) and `hne` (the contract) of `final_modulo_items5` are gone. The constants
`K D` of `hne` also enter the interface of `hsoj`; there they are `items6K`, `items6D`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- The constant `K` of the label program `tmGLNeConc` in the final program (T4 enters through
its constants `supK`, `supD`). -/
noncomputable def items6K (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (hO : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    (hcmb : ConstructiveMembership) (hv : VectorStabilizer) (hni : NormalizedIntersection)
    (hsy : SylowAlgo) (hnc : NormalClosure) (hsc : SylowConjugate) : ℕ :=
  tmGLNeK hst hm hfac hO hh hn hcmb hv
    (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))
    (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))

/-- The constant `D` of the label program `tmGLNeConc` in the final program. -/
noncomputable def items6D (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (hO : GroupOrder) (hh : HermiteFullRank) (hn : SmithNonsingular)
    (hcmb : ConstructiveMembership) (hv : VectorStabilizer) (hni : NormalizedIntersection)
    (hsy : SylowAlgo) (hnc : NormalClosure) (hsc : SylowConjugate) : ℕ :=
  tmGLNeD hst hm hfac hO hh hn hcmb hv
    (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))
    (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))

theorem items6_neF_room : (tmGLNeConc (flcLabIdx + 1) flSupIdx).length + 1 ≤ flcJOff - flcLabOff := by
  rw [length_tmGLNeConc]; unfold flcJOff flcLabOff; omega

/-- Stage 2 from the remaining program contracts and cited tasks. -/
theorem final_modulo_items6 (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hsc : SylowConjugate)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement) (h6 : GI.Cited.SixTransitiveContainsAlt)
    (hDl : GI.Cited.DesignLemma) (hk : KaryRefinement P₀.κ) (h2 : KaryRefinement 2) (ext''' : List Prim)
    (gObjF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (sojF : List Expr) (hsojF : sojF.length ≤ 99000)
    {Kg Dg : ℕ} (Xs : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hsoj : ∀ Kj Dj : ℕ, ItciSojSpec (fagIface hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (3 * items6K hst hm hfac hO hh hn hcmb hv hni hsy hnc hsc + 100)
        (items6D hst hm hfac hO hh hn hcmb hv hni hsy hnc hsc + 1)
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm)
          (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 (itCfObjCo hst) (itCfObjDo hst) (fc10Xp Xs)))))
      (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) asmF (fitC23Idx + 101000) (fitC23Idx + 101001) (fitC23Idx + 101002) Xs)
    (hXs : PBU fun _ W _ => Xs W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF :=
    ⟨tmRi_recF_fits hgo, tmGLPLabF_fits items6_neF_room, tmJFinF_fits⟩
  have hg : gsGen.length ≤ asmSlot := by rw [length_gsGen]; unfold asmSlot; omega
  have hat := flc_hasAt_ne (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (hmb := hmb)
    (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc) (hni := hni) (hsy := hsy)
    (hsc := hsc) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
    (agg := fagAgg fcrE fcmE fitE fcrF fcmF
      (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) hg hF
  have hsup : Iface.TermSupSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
        (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx))
        tmJFinF fcrE fcmE fitE fcrF fcmF
        (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx)))
      (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))
      (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc)) flSupIdx :=
    fl_termSupSpec (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (hmb := hmb) (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc) (hni := hni)
    (hsy := hsy) (hsc := hsc) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
    (agg := fagAgg fcrE fcmE fitE fcrF fcmF
      (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx))) hg (length_flcCos hF)
  have hne : Iface.TmGLPNeSpec (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')))
        (tmRiRecF flcRecIdx 14 8 1 gObjF) (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx))
        tmJFinF fcrE fcmE fitE fcrF fcmF
        (fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx)))
      (items6K hst hm hfac hO hh hn hcmb hv hni hsy hnc hsc)
      (items6D hst hm hfac hO hh hn hcmb hv hni hsy hnc hsc) (flcLabIdx + 1) :=
    tmGLN_conc_spec hst hm hfac hO hh hn hcmb hv hat rfl rfl rfl rfl rfl rfl rfl rfl hsup
  exact final_modulo_items5 hcite hst hm hpre hfac hmb hO hC hAb hOut hTr hcs hder hqc hni hsy
    hsc hnc hs hh hn hcmb hv dixon hK h6 hDl hk h2 ext''' gObjF
    (tmGLNeConc (flcLabIdx + 1) flSupIdx) hgo items6_neF_room sojF hsojF Xs hgl hne hsoj hXs

end GI.Assembly
