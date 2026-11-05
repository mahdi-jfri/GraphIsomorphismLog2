module

public import Workspace.Assembly.CmpReq
public import Workspace.Impl.FinLayoutCertPrims

@[expose] public section

/-!
# Stage 2 with the primitive of the round at index 19

`final_modulo_cmp` holds for every tail `ext'` of the primitive table after the A.20 block. The
items phase calls the cited joint refinement `KaryRefinement P₀.κ` (`stRef_spec`), so its
contract `AsItemsOK` can only be proved for a program that has this primitive. Here we fix the
tail to `aggExtra hk ++ ext''`, which puts `karyRefinementPrim hk` at index `19`
(`fcr_prim_kary`), and take `hk : KaryRefinement P₀.κ` as a hypothesis. The statement is
`final_modulo_cmp` for this tail.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23 and the items, with the joint refinement at primitive `19`.** T2, T4, the coset program T4–T6, the A.20 recursion, the reading,
the certificate phase and the comparison phase of the round are programs. -/
theorem final_modulo_cmp_k (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (hs : SolvableCosetIntersection) (hh : HermiteFullRank)
    (hn : SmithNonsingular) (hcmb : ConstructiveMembership) (hv : VectorStabilizer)
    (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) (hk : KaryRefinement P₀.κ) (ext'' : List Prim)
    (gObjF labF jF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    (hlF : labF.length ≤ flcJOff - flcLabOff) (hjF : jF.length ≤ flSupOff - flcJOff)
    {Kl Dl Kj Dj Kg Dg : ℕ} (itE : Expr) (itF : List Expr) (Xi : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      fcmE itE fcrF fcmF itF) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE
      fcmE itE fcrF fcmF itF) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE fcmE
      itE fcrF fcmF itF) Kj Dj flcJIdx)
    (hi : AsItemsOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE fcmE
        itE fcrF fcmF itF) asmF asHandImpl Xi (asb 4))
    (hXi : PBU fun _ W _ => Xi W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_cmp hst hm hpre hfac hmb hO hC hAb hTr hder hni hnc hs
    hh hn hcmb hv dixon hK hDl (aggExtra hk ++ ext'') gObjF labF jF hgo hlF hjF itE itF Xi hgl
    hlab hjj hi hXi

end GI.Assembly
