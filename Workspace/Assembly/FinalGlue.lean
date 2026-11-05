module

public import Workspace.Assembly.FinalContracts
public import Workspace.Impl.FinLayoutSoj

@[expose] public section

/-!
# Stage 2 from the object glue

`final_modulo_glueObj` is `final_modulo_contracts` with the first-rectangle item placed
(the name `final_modulo_glue` is taken by an earlier step, `GlueReq.lean`):
`sojF := fc11SojF`, the table `fc11Conc` of the first-rectangle programs at `fitC23Idx + 101000`
(`Workspace/Impl/FinLayoutSoj.lean`). Its contract `ItciSojSpec` comes from `itcs_soj_spec_pbu`.
That theorem needs two rectangle contracts of the same program:
* the certificate search at `fitRcIdx`, with bound `rcCertB` (`fit_rcCertSpec_final`);
* the representation program at `fitRpIdx`, with bound `rcRB` (`rcR_fit_repSpec_final`).

The only remaining hypotheses are the object glue: `gObjF`, its length bound `hgo` and its
contract `hgl` (`TermGlueObjSpec`).
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper GI.Impl

/-- **The list of the first-rectangle item**: its table at its final base. -/
noncomputable def fc11SojF : List Expr := fc11Conc (fitC23Idx + 101000)

theorem fc11SojF_length : fc11SojF.length ≤ 99000 := by
  rw [fc11SojF, fc11Conc_length]; decide

theorem fc11_rcCertB_pbu : PBU fun _ W _ => rcCertB W := by
  unfold rcCertB
  exact PBU.smul _ (PBU.pow (PBU.addc PBU.W 21) 40)

/-- The weight bound of the first-rectangle item. -/
noncomputable def fc11Xs : ℕ → ℕ :=
  itcsXs (normalizedFactorPrim GI.Proved.normalizedFactor) rcCertB (rcRB GI.Proved.pointwiseStab GI.Proved.preimage)
    fc11_rcCertB_pbu (rcRB_pbu GI.Proved.pointwiseStab GI.Proved.preimage)

/-- **Facts of the final program** for any first-rectangle list that fits its room: the list
sits at `fitC23Idx + 101000`, and the certificate search and the representation program meet
their contracts. -/
theorem fc11_prog_parts {gObjF sojF : List Expr}
    (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff) (hsojF : sojF.length ≤ 99000) :
    (cProg gObjF sojF).HasAt (fitC23Idx + 101000) sojF ∧
      RcCertSpec (cProg gObjF sojF) fitRcIdx rcCertB ∧
      RcRepSpec (cProg gObjF sojF) fitRpIdx (rcRB GI.Proved.pointwiseStab GI.Proved.preimage) := by
  have hprF := fc10PrF_fits hsojF
  have hF : FlcFits (tmRiRecF flcRecIdx 14 8 1 gObjF)
      (tmGLPLabF (tmGLNeConc (flcLabIdx + 1) flSupIdx)) tmJFinF :=
    ⟨tmRi_recF_fits hgo, tmGLPLabF_fits items6_neF_room, tmJFinF_fits⟩
  have hfit : FitFits itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx) :=
    rcR_fits itHvHvIF_fits (fc23_fits fc23ObF_length hprF)
  obtain ⟨_, _, _, _, _, _, _, hit⟩ := fag_hasAt (hst := GI.Proved.pointwiseStab) (hm := GI.Proved.membership)
    (hpre := GI.Proved.preimage) (hfac := GI.Proved.normalizedFactor) (hmb := GI.Proved.minimalBlocks) (hO := GI.Proved.groupOrder)
    (hC := finCam GI.Proved.johnsonIdentification GI.Proved.groupOrder)
    (hder := GI.Proved.derivedSubgroup)
    (hni := GI.Proved.normalizedIntersection)
    (hnc := GI.Proved.normalClosure)
    (ext := finExt GI.Proved.solvableCosetIntersection GI.Proved.hermiteFullRank GI.Proved.smithNonsingular
      GI.Proved.constructiveMembership GI.Proved.vectorStabilizer GI.Proved.karyRefinement64 GI.Proved.karyRefinement2)
    hF (crE := fcrE) (cmE := fcmE) (itE := fitE)
    (itF := fitF itHvHvIF (fc23F fc23ObF (fc10PrF sojF)) (rcRepF fitRpIdx)) ⟨fcr_fits, fcm_fits⟩
  obtain ⟨_, _, hc23, _⟩ := fit_hasAt_parts hfit hit
  have hpr := (fc23_parts fc23ObF_length hc23).2.2
  refine ⟨?_, fit_rcCertSpec_final GI.Proved.karyRefinement64 hF ⟨fcr_fits, fcm_fits⟩ hfit,
    rcR_fit_repSpec_final GI.Proved.karyRefinement64 hF ⟨fcr_fits, fcm_fits⟩ itHvHvIF_fits
      (fc23_fits fc23ObF_length hprF)⟩
  have hc : (fc10Conc (fitC23Idx + 100000)).length ≤ 1000 := by rw [fc10Conc_length]; decide
  have hpr' := hpr.right
  rw [length_asmPad hc, Nat.add_assoc] at hpr'
  exact hpr'

/-- **The table of the first-rectangle item is installed** in the final program, for every
object glue `gObjF` that fits its room. -/
theorem fc11_sojOk_final {gObjF : List Expr}
    (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff) :
    itcsSojOk (cProg gObjF fc11SojF) (fc11Ix (fitC23Idx + 101000)) GI.Proved.normalizedFactor :=
  fc11_sojOk (fc11_prog_parts hgo fc11SojF_length).1 rfl

/-- **The first-rectangle contract** in the final program, for every interface. -/
theorem fc11_sojSpec (I : Iface) (F : Funs) {gObjF : List Expr}
    (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff) :
    ItciSojSpec I (cProg gObjF fc11SojF) F (fitC23Idx + 101000) (fitC23Idx + 101001)
      (fitC23Idx + 101002) fc11Xs ∧ PBU fun _ W _ => fc11Xs W := by
  obtain ⟨-, hc, hr⟩ := fc11_prog_parts hgo fc11SojF_length
  exact itcs_soj_spec_pbu I F (fc11_sojOk_final hgo) rcCertB (rcRB GI.Proved.pointwiseStab GI.Proved.preimage)
    fc11_rcCertB_pbu (rcRB_pbu GI.Proved.pointwiseStab GI.Proved.preimage) hc hr

/-- **Stage 2 from the object glue.**

Every cited algorithm task is a proved theorem, and the first-rectangle item is the concrete table
`fc11SojF`. The only hypotheses are the object glue `gObjF`, with its length bound `hgo` and
its contract `hgl` (`TermGlueObjSpec` at constants `Kg Dg`). -/
theorem final_modulo_glueObj
    (gObjF : List Expr) (hgo : gObjF.length ≤ flcLabOff - flcRecOff - tmRiGlueOff)
    {Kg Dg : ℕ}
    (hgl : Iface.TermGlueObjSpec (cProg gObjF fc11SojF) Kg Dg (flcRecIdx + tmRiGlueOff)) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final_modulo_contracts gObjF hgo fc11SojF fc11SojF_length fc11Xs hgl
    (fun Kj Dj => (fc11_sojSpec (cIface Kj Dj Kg Dg fc11Xs) asmF hgo).1)
    (fc11_sojSpec (cIface 0 0 Kg Dg fc11Xs) asmF hgo).2

end GI.Assembly
