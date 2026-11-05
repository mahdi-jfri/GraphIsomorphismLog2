module

public import Workspace.Impl.FinLayoutCos
public import Workspace.Assembly.RadReq

@[expose] public section

/-!
# Stage 2 with the coset program T4–T6 in place

`final_modulo_rad` left `TermCosetSpec` for the slot `cos` open. Here the slot holds
`flCos (flcCos recF labF jF)` (`FinLayoutCos.lean`): the coset program at
`rlb rlCosOff`, the A.20 recursion `recF` at `flcRecIdx`, the label coset `labF` at `flcLabIdx`,
the `J`-answer `jF` at `flcJIdx`, and T4 at `flSupIdx`. So `TermCosetSpec` follows from
`flc_termCosetSpec`, with cost exponent `flcA …`. T4 needs three more cited primitives, which
sit at indices `11`–`13` (`flSupExtra`); any list `ext` of further primitives follows, from
index `14` on.

`final_modulo_cos` proves the trusted statement from the cited tasks, the cited result
`DixonDerivedLength` (as a hypothesis), the specs of `recF`, `labF`, `jF` at their indices, the
four phase contracts of the aggregation round and the polynomial bound `PBU X`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure)

/-- **Stage 2 up to the A.20 recursion, the two abelian computations of Theorem A.23 and the
phase contracts of the aggregation round.** T2, T4 and the coset program T4–T6 are programs. -/
theorem final_modulo_cos (hst : PointwiseStab)
    (hm : Membership) (hpre : Preimage) (hfac : NormalizedFactor) (hmb : MinimalBlocks)
    (hO : GroupOrder) (hC : CameronRecognition) (hAb : GI.Cited.GMPAbelianFactors)
    (hTr : GI.Cited.GMPTransitiveNonabelian)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection)
    (hnc : NormalClosure) (dixon : GI.Cited.DixonDerivedLength) (ext : List Prim)
    (recF labF jF : List Expr) (hF : FlcFits recF labF jF) {Kl Dl Kj Dj Kc Dc : ℕ}
    (H : AsHand) (X : ℕ → ℕ) (rd cr cm it : Expr) (rest : List Expr)
    (hrec : Iface.TermRecSpec (flcProg hst hm hpre hfac hmb hO hC hder hni hnc
      ext gsGen recF labF jF (asAgg rd cr cm it rest)) Kc Dc flcRecIdx)
    (hlab : Iface.TermGlueLabSpec (flcProg hst hm hpre hfac hmb hO hC hder hni
      hnc ext gsGen recF labF jF (asAgg rd cr cm it rest)) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext
      gsGen recF labF jF (asAgg rd cr cm it rest)) Kj Dj flcJIdx)
    (hrd : AsReadOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hder hni hm hpre hO)
        (flRadD hder hni hm hpre hO) (flcA hst hm hpre hO hder hni hnc Kl Dl Kj Dj Kc
          Dc))) (asWa hst hm hpre hfac X)).iface
      (flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext gsGen recF labF jF
        (asAgg rd cr cm it rest)) asmF H X (asb 1))
    (hct : AsCertOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hder hni hm hpre hO)
        (flRadD hder hni hm hpre hO) (flcA hst hm hpre hO hder hni hnc Kl Dl Kj Dj Kc
          Dc))) (asWa hst hm hpre hfac X)).iface
      (flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext gsGen recF labF jF
        (asAgg rd cr cm it rest)) asmF H X (asb 2))
    (hcm : AsCompOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hder hni hm hpre hO)
        (flRadD hder hni hm hpre hO) (flcA hst hm hpre hO hder hni hnc Kl Dl Kj Dj Kc
          Dc))) (asWa hst hm hpre hfac X)).iface
      (flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext gsGen recF labF jF
        (asAgg rd cr cm it rest)) asmF H X (asb 3))
    (hi : AsItemsOK (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
      (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hder hni hm hpre hO)
        (flRadD hder hni hm hpre hO) (flcA hst hm hpre hO hder hni hnc Kl Dl Kj Dj Kc
          Dc))) (asWa hst hm hpre hfac X)).iface
      (flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext gsGen recF labF jF
        (asAgg rd cr cm it rest)) asmF H X (asb 4))
    (hX : PBU fun _ W _ => X W) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_rad hst hm hpre hfac hmb hO hC hAb hTr hder hni
    (flSupExtra hnc ++ ext) (flCos (flcCos recF labF jF))
    (length_flCos (length_flcCos hF)) H X rd cr cm it rest
    (flc_termCosetSpec dixon (by rw [length_gsGen]; unfold asmSlot; omega) hF hrec hlab hjj)
    hrd hct hcm hi hX

end GI.Assembly
