import Workspace.Impl.AggRectRepT12
import Workspace.Impl.TermRecPoly

/-!
# The rectangle representation program meets its contract

`rcR_repSpec`: for an index layout `J` with `RcROk P J`, PointwiseStab at `J.jp` and Preimage at
`J.jpre`, the main function meets `RcRepSpec` with the bound `rcRB hst hpre`, and this bound is
polynomial (`rcRB_pbu`).

The representation function is `rcRRf e I hx`, with `x` the first point of the domain
(`rcR_first_dom`). The proof splits on the small list of `π(G_x)` (`rcR_small_cases`): two labels
(`rcR_case_pair`) or one label (`rcR_case_car`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (Val gens encPerm encGroup encPts PointwiseStab Preimage)

/-- The stage bound for the input weight `n`. -/
def rcRWb (n : ℕ) : ℕ := 10 ^ 6 * (n + 1) ^ 10

/-- **The bound of the program** on inputs of weight `n`. -/
noncomputable def rcRB (hst : PointwiseStab) (hpre : Preimage) (n : ℕ) : ℕ :=
  rcRCostM hst hpre (rcRWb n) + rcRWb n

/-- **The contract of the rectangle representation program.** -/
theorem rcR_repSpec {P : Program} {J : RcRIdx} (ok : RcROk P J) (hst : PointwiseStab)
    (hj : P.prims[J.jp]? = some (pointwiseStabPrim hst)) (hpre : Preimage)
    (hjp : P.prims[J.jpre]? = some (preimagePrim hpre)) :
    RcRepSpec P J.main (rcRB hst hpre) := by
  intro Ω C k e c S sv L I ps _ hcan hps
  obtain ⟨gv, dv, xv, yv, hv, rv, -, hD, -, -, -, hR, rfl⟩ := hcan.val
  have hfin : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨x, hx, hxd⟩ := rcR_first_dom e I
  refine ⟨rcRRf e I hx, fun W R hc => ?_⟩
  have hdv : dv = natList (rcRL (rcRDom e S)) := by
    rw [hD, rcR_encFun_eq]
  subst hdv
  have hIn : rcRepIn (.list [.nat k, gv, natList (rcRL (rcRDom e S)), xv, yv, hv, rv,
      boolVal S.floor, .nat S.h, .nat S.N]) L.q ps W R =
      rcRInV [.nat k, gv, natList (rcRL (rcRDom e S)), xv, yv, hv, rv, boolVal S.floor,
        .nat S.h, .nat S.N] ps W R := by
    unfold rcRepIn; rw [rcR_setVal_eq, rcR_setVal_eq]
  rw [hIn]
  have key : CpFB P J.main (rcRInV [.nat k, gv, natList (rcRL (rcRDom e S)), xv, yv, hv, rv,
      boolVal S.floor, .nat S.h, .nat S.N] ps W R)
      (rcRWb (rcRInV [.nat k, gv, natList (rcRL (rcRDom e S)), xv, yv, hv, rv,
        boolVal S.floor, .nat S.h, .nat S.N] ps W R).wt)
      (rcRCostM hst hpre (rcRWb (rcRInV [.nat k, gv, natList (rcRL (rcRDom e S)), xv, yv, hv,
        rv, boolVal S.floor, .nat S.h, .nat S.N] ps W R).wt))
      (fun w => ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
        w = rcRepVal e (rcRRf e I hx W R hc) hs ∧ PairGens e L (rcRRf e I hx W R hc).H hs ∧
          hs.length ≤ k ^ 2) := by
    rcases rcR_small_cases I hx hc.1 with ⟨a, hsm⟩ | ⟨d₁, d₂, hlt, hsm⟩
    · exact rcR_case_car e I hx hc ok hst hj hpre hjp hps _ rfl rfl rfl hR hxd hsm le_rfl le_rfl
    · exact rcR_case_pair e I hx hc ok hst hj hpre hjp hps _ rfl rfl hxd hlt hsm le_rfl le_rfl
  refine FunAll.mono key fun w cost h => ?_
  obtain ⟨⟨hs, h1, h2, h3⟩, hw, hcost⟩ := h
  refine ⟨hs, h1, h2, h3, ?_, ?_⟩
  · unfold rcRB; omega
  · unfold rcRB; omega

/-- **The bound is polynomial.** -/
theorem rcRB_pbu (hst : PointwiseStab) (hpre : Preimage) :
    PBU fun _ W _ => rcRB hst hpre W := by
  have hw : PBU fun _ W _ => rcRWb W := PBU.smul _ (PBU.pow (PBU.addc PBU.W 1) 10)
  have hp : ∀ d, PBU fun _ W _ => (rcRWb W + 1) ^ d := fun d => PBU.pow (PBU.addc hw 1) d
  refine PBU.mono (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add (PBU.add
    (PBU.add (tmRiP_bs (pointwiseStabPrim hst) hw) (PBU.smul (10 ^ 22) (hp 8)))
    (PBU.smul (10 ^ 11) (hp 12)))
    (PBU.smul 2 (PBU.add (tmRiP_bs (preimagePrim hpre) hw) (PBU.smul (10 ^ 18) (hp 8)))))
    (PBU.add (tmRiP_bs (pointwiseStabPrim hst) hw) (PBU.smul (10 ^ 26) (hp 9))))
    (PBU.smul 100 hw)) (PBU.const 100)) hw) fun _ W _ => le_of_eq ?_
  rfl

end GI.Impl
