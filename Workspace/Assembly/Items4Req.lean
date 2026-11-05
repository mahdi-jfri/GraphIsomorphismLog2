module

public import Workspace.Assembly.Items3Req
public import Workspace.Impl.TermJFin

@[expose] public section

/-!
# Stage 2 with the concrete `J`-answer

`final_modulo_items4` is `final_modulo_items3` with the `J`-answer made concrete,
`jF := tmJFinF` (`TermJFin.lean`). Its room bound is `tmJFinF_fits`, and its contract
`TermJSpec` is `tmJ_final`. The constants `Kj Dj` of `tmJ_final` are only known to exist, so the
pair-part contract `hpair` is asked for every `Kj Dj`. The interfaces `fagIface … Kj Dj …` differ
only in the work bound `W`, and the pair part has its own bound `Xp (I.inW .giant S)`, which does
not depend on `W`. The pair-part contract is proved for a general interface
(`itci_pairSpec_of`).

The remaining contracts describe the pair branch, the nonempty label program and the A.20 glue.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- Stage 2 from the remaining program contracts and cited tasks. -/
theorem final_modulo_items4 (hst : PointwiseStab)
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
    (cfPrF : List Expr) (hprF : cfPrF.length ≤ 100000)
    {K D Kg Dg : ℕ} (Xp : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hne : Iface.TmGLPNeSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) K D (flcLabIdx + 1))
    (hpair : ∀ Kj Dj : ℕ, ItciPairSpec (fagIface hst hm hpre hfac hmb hO hC hder hni hnc (3 * K + 100) (D + 1)
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm)
          (fitXi hk hst hO (itHvXh hfac hst) (fc23X h2 (itCfObjCo hst) (itCfObjDo hst) Xp))))
      (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ (karyRefinementPrim h2 :: ext'''))) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF neF) tmJFinF fcrE fcmE fitE fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF cfPrF) (rcRepF fitRpIdx))) asmF (fitC23Idx + 100000) (fitC23Idx + 100001) (fitC23Idx + 100002) Xp)
    (hXp : PBU fun _ W _ => Xp W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  obtain ⟨Kj, Dj, hT⟩ := tmJ_final hst hm hfac hO hni hh hcmb
  exact final_modulo_items3 hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl hk h2 ext''' gObjF neF tmJFinF hgo hneF
    tmJFinF_fits cfPrF hprF Xp hgl hne
    (hT hpre hmb hC hder hnc hs hn hv
      (aggExtra hk ++ (karyRefinementPrim h2 :: ext''')) _ _ fcrE fcmE fitE fcrF fcmF _
      (tmRi_recF_fits hgo) (tmGLPLabF_fits hneF))
    (hpair Kj Dj) hXp

end GI.Assembly
