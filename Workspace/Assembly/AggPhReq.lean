module

public import Workspace.Impl.FinLayoutAgg
public import Workspace.Assembly.CosReq

@[expose] public section

/-!
# Stage 2 with the reading of the aggregation round in place

`final_modulo_cos` left the hand-over data `AsHand`, the four phase contracts of the round and
the polynomial bound of the phases open. Here:

* the hand-over is `asHandImpl` (`CpHand`, `CmHand`, `ItHand`, `FinLayoutAgg.lean`);
* the round is `fagAgg crE cmE itE crF cmF itF`: the reading at `asb 1` with its
  module at `fagRdIdx`, the entries of the other three phases at `asb 2`, `asb 3`, `asb 4` and
  their helper lists at `fagCrIdx`, `fagCmIdx`, `fagItIdx`;
* `AsReadOK` is proved (`fag_asReadOK`), with the cited results that `rd_asReadOK` uses;
* each other phase has its own bound `Xc`, `Xm`, `Xi`; the round uses their sum with the bound of
  the reading (`fagX`), and the sum is polynomial when the three bounds are (`fag_pbu`).

The phase contracts are stated for the interface `fagIface … (fagX hpre Xc Xm Xi)`, which is the
interface of `final_modulo_cos` for this bound.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure)

/-- **Stage 2 up to the A.20 recursion, the two abelian computations of Theorem A.23 and three
phases of the aggregation round** (the certificate phase, the comparison phase and the items).
T2, T4, the coset program T4–T6 and the reading of the round are programs. -/
theorem final_modulo_aggph (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (dixon : GI.Cited.DixonDerivedLength)
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) (ext : List Prim)
    (recF labF jF : List Expr) (hF : FlcFits recF labF jF) {Kl Dl Kj Dj Kc Dc : ℕ}
    (crE cmE itE : Expr) (crF cmF itF : List Expr) (hA : FagFits crF cmF)
    (Xc Xm Xi : ℕ → ℕ)
    (hrec : Iface.TermRecSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      ext recF labF jF crE cmE itE crF cmF itF) Kc Dc flcRecIdx)
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc ext recF labF jF crE cmE itE crF cmF itF) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext
      recF labF jF crE cmE itE crF cmF itF) Kj Dj flcJIdx)
    (hct : AsCertOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        Kc Dc (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xc (asb 2))
    (hcm : AsCompOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        Kc Dc (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xm (asb 3))
    (hi : AsItemsOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj
        Kc Dc (fagX hpre Xc Xm Xi))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl Xi (asb 4))
    (hXc : PBU fun _ W _ => Xc W) (hXm : PBU fun _ W _ => Xm W) (hXi : PBU fun _ W _ => Xi W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_cos hst hm hpre hfac hmb hO hC hAb hTr hder hni hnc
    dixon ext recF labF jF hF asHandImpl (fagX hpre Xc Xm Xi) (rdF fagRdIdx) crE cmE itE
    (fagRest crF cmF itF) hrec hlab hjj
    (fag_asReadOK hK hDl hF hA (fag_le_rd hpre Xc Xm Xi))
    (fag_asCertOK_mono hct (fag_le_c hpre Xc Xm Xi))
    (fag_asCompOK_mono hcm (fag_le_m hpre Xc Xm Xi))
    (fag_asItemsOK_mono hi (fag_le_i hpre Xc Xm Xi))
    (fag_pbu hpre hXc hXm hXi)

end GI.Assembly
