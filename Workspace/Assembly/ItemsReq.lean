module

public import Workspace.Assembly.CmpReqK
public import Workspace.Impl.FinLayoutItemsOK

@[expose] public section

/-!
# Stage 2 with the items in place

`final_modulo_cmp_k` left the items of the aggregation round open: an entry `itE` at `asb 4`,
a list `itF` at `fagItIdx`, a bound `Xi`, the contract `AsItemsOK` and the growth `PBU` of `Xi`.
Here we fill them with the layout of `FinLayoutItemsOK.lean`: `itE := fitE`,
`itF := fitF hvIF c23F rpF` and `Xi := fitXi hk hst hO Xh X3`. The programs of the items that
are written (the structure step, the run, Case 1, the branch step of Case 2a, the certificate
search) are fixed. Three lists are not written yet, and stay parameters with their room:

* `hvIF` at `fitHvIdx`: the init program of Case 2a, with its contract `ItHvInitOK` and bound
  `Xh`;
* `c23F` at `fitC23Idx`: the programs of Cases 2b and 3 (init at `fitC23Idx`, branch step at
  `fitC23Idx + 1`), with their contract `ItSCaseOK` and bound `X3`;
* `rpF` at `fitRpIdx`: the rectangle representation program. Its contract `RcRepSpec` is not a
  hypothesis here: only the programs of Cases 2b and 3 call it, so the proof of their `ItSCaseOK` takes
  `RcRepSpec … fitRpIdx …` as a hypothesis, together with
  `fit_rcCertSpec_final` for the certificate search at `fitRcIdx`.

The contract `AsItemsOK` is `fit_asItemsOK`, which holds for every interface. The growth of the
bound is `fit_Xi_pbu`.

From this step on, the chain also returns `RoundOK` for the interface of the solved program: the
contracts of the reading, of the structure step and of the three cases. The degree-sensitive
algorithm has its own copies of the other phases, which call these programs of the round. They are
proved here by the same lemmas that `fit_asItemsOK` and `final_modulo_aggph` use.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

/-- **The contracts of the round that the degree-sensitive algorithm reuses**, at their places in
the final layout, each with a polynomial bound: the reading at `asb 1`, the structure step of the
items at `fagItIdx`, and the three cases (Case 1 at `fagItIdx + 38`, `fagItIdx + 39`; Case 2a at
`fitHvIdx`, `fagItIdx + 59`; Cases 2b and 3 at `fitC23Idx`, `fitC23Idx + 1`). -/
def RoundOK (I : Iface) (Pg : Program) : Prop :=
  (∃ X : ℕ → ℕ, (PBU fun _ W _ => X W) ∧ AsReadOK I Pg asmF asHandImpl X (asb 1)) ∧
  (∃ Xs : ℕ → ℕ, (PBU fun _ W _ => Xs W) ∧ ItSStrOK I Pg asmF (fagItIdx + 0) Xs) ∧
  ∃ Xc : ℕ → ℕ, (PBU fun _ W _ => Xc W) ∧
    ItSCaseOK I Pg asmF (· = .one) (fagItIdx + 38) (fagItIdx + 39) Xc ∧
    ItSCaseOK I Pg asmF (· = .twoA) fitHvIdx (fagItIdx + 59) Xc ∧
    ItSCaseOK I Pg asmF (fun a => a = .twoB ∨ a = .three) fitC23Idx (fitC23Idx + 1) Xc

/-- **`Solved` with the contracts of the round** for its interface. -/
def SolvedR (Pg : Program) : Prop := SolvedQ Pg fun I => RoundOK I Pg

theorem SolvedR.solved {Pg : Program} (h : SolvedR Pg) : Solved Pg := SolvedQ.solved h

/-- **Stage 2 up to the glue program of Lemma A.20, the two abelian computations of
Theorem A.23, the init program of Case 2a, the programs of Cases 2b and 3, and the rectangle
representation program.** T2, T4, the coset program T4–T6, the A.20 recursion, the reading, the
certificate phase, the comparison phase, the structure step and the run of the items, Case 1, the
branch step of Case 2a and the certificate search are programs. -/
theorem final_modulo_items (hst : PointwiseStab)
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
    (hvIF c23F rpF : List Expr) (hhv : hvIF.length ≤ fitC23Off - fitHvOff)
    (hc23 : c23F.length ≤ fitRpOff - fitC23Off) (hrp : rpF.length ≤ fitRoom - fitRpOff)
    {Kl Dl Kj Dj Kg Dg : ℕ} (Xh X3 : ℕ → ℕ)
    (hgl : Iface.TermGlueObjSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kg Dg (flcRecIdx + tmRiGlueOff))
    (hlab : Iface.TermGlueLabSpec (fagProg hst hm hpre hfac hmb hO hC hder hni
      hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
      labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) Kj Dj flcJIdx)
    (hinit : ItHvInitOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) (fitXi hk hst hO Xh X3)))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
        labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) asmF fitHvIdx Xh)
    (hXh : PBU fun _ W _ => Xh W)
    (h23 : ItSCaseOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl
        Kj Dj (fglRecK hs hder hm Kg Dg) (fglRecD hs hder hm Kg Dg)
        (fagX hpre (cpCertX hst hpre hm) (cmRunX hst hpre hm) (fitXi hk hst hO Xh X3)))
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
        (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF)
        labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) asmF
      (fun a => a = .twoB ∨ a = .three) fitC23Idx (fitC23Idx + 1) X3)
    (hX3 : PBU fun _ W _ => X3 W) :
    SolvedR
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF fcrE fcmE fitE fcrF fcmF (fitF hvIF c23F rpF)) := by
  -- the room of the coset slot and of the two phase lists, as in `final_modulo_cmp`
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF) labF jF :=
    ⟨tmRi_recF_fits hgo, hlF, hjF⟩
  -- the items' list sits at `fagItIdx`, and its fixed part meets `FitAt`
  obtain ⟨-, -, -, -, -, -, -, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) hF (crE := fcrE) (cmE := fcmE)
    (itE := fitE) (itF := fitF hvIF c23F rpF) ⟨fcr_fits, fcm_fits⟩
  obtain ⟨hC', -, -, -⟩ := fit_hasAt_parts ⟨hhv, hc23, hrp⟩ hit
  have h := final_modulo_cmp_k hst hm hpre hfac hmb hO hC hAb hTr hder hni
    hnc hs hh hn hcmb hv dixon hK hDl hk ext'' gObjF labF jF hgo hlF hjF fitE
    (fitF hvIF c23F rpF) (fitXi hk hst hO Xh X3) hgl hlab hjj
    -- the items, for the interface of `final_modulo_cmp_k` (`fit_asItemsOK`)
    (fit_asItemsOK hk hF ⟨fcr_fits, fcm_fits⟩ ⟨hhv, hc23, hrp⟩ _ hinit h23)
    (fit_Xi_pbu hk hst hO hXh hX3)
  refine h.mono fun I hI => ?_
  subst hI
  -- the three case contracts at the common bound `fitXc`, as in `fit_asItemsOK`
  exact ⟨⟨rdX hpre, rd_pbu hpre, fag_asReadOK hK hDl hF ⟨fcr_fits, fcm_fits⟩ fun _ => le_rfl⟩,
    ⟨itSXs hk hst hO, itS_Xs_pbu hk hst hO,
      fit_strOK hC' hk hst hO fcr_prim_kary rfl rfl _ asmF⟩,
    fitXc Xh X3, (PBU.add (PBU.add itS_sc1X_pbu (fit_hvX_pbu hXh)) hX3).mono
      fun _ _ _ => le_of_eq rfl,
    ItSCaseOK.mono _ _ (fit_c1 hC' _ asmF) fun W => by unfold fitXc; omega,
    ItSCaseOK.mono _ _ (fit_c2a hC' _ asmF hinit) fun W => by unfold fitXc; omega,
    ItSCaseOK.mono _ _ h23 fun W => by unfold fitXc; omega⟩

end GI.Assembly
