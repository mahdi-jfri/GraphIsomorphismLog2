import Workspace.Impl.FinLayoutRad
import Workspace.Assembly.RowReq

/-!
# Stage 2 with the radical preimage T2 as a program

`final_modulo_row_agg` left two pieces of the row terminal open: T2, the radical preimage
(`TermRadSpec`), and T4–T6, one radical coset (`TermCosetSpec`). Here the slot `rad` holds the
program `flRad` of T2 (`FinLayoutRad.lean`), so T2 is proved (`fl_termRadSpec`, from
`rad_termRadSpec`). The program needs four more cited primitives, which sit at
indices `7`–`10` of the table (`flRadExtra`): ChiefSeriesAlgo, DerivedSubgroup,
QuotientCentralizer, NormalizedIntersection.

`final_modulo_rad` proves the trusted statement from the cited tasks, `TermCosetSpec` for the
code `cos`, the four phase contracts of the aggregation round and the polynomial bound `PBU X`.
Any list `ext` of further primitives may follow, from index `11` on (for T4–T6).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection)

/-- **Stage 2 up to one radical coset (T4–T6) and the phase contracts of the aggregation
round.** T2 is the program `flRad`. -/
theorem final_modulo_rad (hcite : GI.Cited.TransitiveAffected) (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hOut : GI.Cited.GMPOutBound) (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (ext : List Prim) (cos : List Expr)
    (hc : cos.length ≤ asmSlot - rlCosOff) {Ac : ℝ}
    (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr) (rest : List Expr)
    (hcos : Iface.TermCosetSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext)) gsGen
        (rlRow flRad cos) (asAgg rd cr cm it rest)) Ac (rlb rlCosOff))
    (hrd : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hcs hder hqc hni hm)
        (flRadD hcs hder hqc hni hm) Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext)) gsGen
        (rlRow flRad cos) (asAgg rd cr cm it rest)) asmF H X (asb 1))
    (hct : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hcs hder hqc hni hm)
        (flRadD hcs hder hqc hni hm) Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext)) gsGen
        (rlRow flRad cos) (asAgg rd cr cm it rest)) asmF H X (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hcs hder hqc hni hm)
        (flRadD hcs hder hqc hni hm) Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext)) gsGen
        (rlRow flRad cos) (asAgg rd cr cm it rest)) asmF H X (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hcs hder hqc hni hm)
        (flRadD hcs hder hqc hni hm) Ac)) (asWa hst hm hpre hfac X)).iface
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext)) gsGen
        (rlRow flRad cos) (asAgg rd cr cm it rest)) asmF H X (asb 4))
    (hX : PBU fun _ W _ => X W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_row_agg_ext hcite hst hm hpre hfac hmb hO hC hAb hOut hTr
    (flRadExtra hcs hder hqc hni ++ ext) flRad cos length_flRad hc H X rd cr cm it rest
    (fl_termRadSpec (by rw [length_gsGen]; unfold asmSlot; omega) hc) hcos hrd hct hcm hi hX

end GI.Assembly
