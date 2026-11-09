module

public import Workspace.Degree.LayoutTrans

@[expose] public section

/-!
# The placements of `giantD` in `degProg`

`giantD` at `dgb 20` is the round `aggBodyE` of the general algorithm with new entries of the
certificate phase, the comparison phase and the items, and a new map of the children. The entries
call new runners `runBody degF …`; every other part is the code of the general algorithm.

The interface is the one of the solved final program, `mI` (`finalProg_solvedR`). The contracts
of the reading, the structure step and the three cases come from `RoundOK` for `mI`, with bounds
`mXr`, `mXs`, `mXc`. They hold in `degProg` by `Degree/RoundOK.lean`.

`dp_giantCode` gives `GiantCode` for `degProg`, with the phase bound `dpXw`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val)

set_option maxRecDepth 100000

variable {h : JohnsonRecognition} {E D : ℕ}

/-! ### The interface of the solved final program -/

theorem mRound : ∃ R : Rest, RoundOK R.iface (cProg mainGObjF fc11SojF) ∧
    ∀ (m : Mode) {Ω C : Type} (S : State Ω C), R.iface.IH (cProg mainGObjF fc11SojF) asmF m S :=
  SolvedQ.ih_all finalProg_solvedR

/-- The rest of the solved final program. -/
noncomputable def mR : Rest := Classical.choose mRound

/-- **The interface of the solved final program.** -/
noncomputable abbrev mI : Iface := mR.iface

theorem mR_round : RoundOK mI (cProg mainGObjF fc11SojF) := (Classical.choose_spec mRound).1

theorem mR_ih (m : Mode) {Ω C : Type} (S : State Ω C) :
    mI.IH (cProg mainGObjF fc11SojF) asmF m S :=
  (Classical.choose_spec mRound).2 m S

/-- The bound of the reading. -/
noncomputable def mXr : ℕ → ℕ := Classical.choose mR_round.1

theorem mXr_spec : (PBU fun _ W _ => mXr W) ∧
    AsReadOK mI (cProg mainGObjF fc11SojF) asmF asHandImpl mXr (asb 1) :=
  Classical.choose_spec mR_round.1

/-- The bound of the structure step. -/
noncomputable def mXs : ℕ → ℕ := Classical.choose mR_round.2.1

theorem mXs_spec : (PBU fun _ W _ => mXs W) ∧
    ItSStrOK mI (cProg mainGObjF fc11SojF) asmF (fagItIdx + 0) mXs :=
  Classical.choose_spec mR_round.2.1

/-- The common bound of the three cases. -/
noncomputable def mXc : ℕ → ℕ := Classical.choose mR_round.2.2

theorem mXc_spec : (PBU fun _ W _ => mXc W) ∧
    ItSCaseOK mI (cProg mainGObjF fc11SojF) asmF (· = .one) (fagItIdx + 38) (fagItIdx + 39) mXc ∧
    ItSCaseOK mI (cProg mainGObjF fc11SojF) asmF (· = .twoA) fitHvIdx (fagItIdx + 59) mXc ∧
    ItSCaseOK mI (cProg mainGObjF fc11SojF) asmF (fun a => a = .twoB ∨ a = .three) fitC23Idx
      (fitC23Idx + 1) mXc :=
  Classical.choose_spec mR_round.2.2

/-- **The phase bound of the round** of the degree algorithm: the sum of the bounds of its four
phases. -/
noncomputable def dpXw (W : ℕ) : ℕ :=
  mXr W + cpCertX GI.Proved.pointwiseStab GI.Proved.preimage GI.Proved.membership W +
    cmRunX GI.Proved.pointwiseStab GI.Proved.preimage GI.Proved.membership W + itSX mXs mXc W

theorem dpXw_pbu : PBU fun _ W _ => dpXw W :=
  PBU.add (PBU.add (PBU.add mXr_spec.1 (cpCertX_pbu _ _ _)) (cm_runX_pbu _ _ _))
    (itS_X_pbu mXs_spec.1 mXc_spec.1)

/-- The induction hypothesis of the general algorithm in `degProg`. -/
theorem dp_ih (m : Mode) {Ω C : Type} (S : State Ω C) : mI.IH (degProg h E D) asmF m S :=
  IH.of_sub cProg_sub_degProg (mR_ih m S)

/-! ### Larger bounds of the phases -/

section Mono

variable {I : Iface} {J : CostT} {Pg : Program} {F₀ F : Funs} {H : AsHand} {X X' : ℕ → ℕ}
  {f : ℕ}

theorem AsCertD.mono (hc : AsCertD I J Pg F₀ F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsCertD I J Pg F₀ F H X' f :=
  fun e c S sv lv L hcall hih Cs st hst => (hc e c S sv lv L hcall hih Cs st hst).mono
    fun _ _ ⟨Ag, hAg, a, ex, h1, h2, h3⟩ => ⟨Ag, hAg, a, ex, h1, h2.trans (by
      have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
      linarith), h3.trans (hX _)⟩

theorem AsCompD.mono (hc : AsCompD I J Pg F₀ F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsCompD I J Pg F₀ F H X' f :=
  fun e c S sv lv L hcall hih Cs st hst => (hc e c S sv lv L hcall hih Cs st hst).mono
    fun _ _ ⟨Ag, hAg, a, ex, h1, h2, h3⟩ => ⟨Ag, hAg, a, ex, h1, h2.trans (by
      have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
      linarith), h3.trans (hX _)⟩

theorem AsItemsD.mono (hc : AsItemsD I J Pg F₀ F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsItemsD I J Pg F₀ F H X' f :=
  fun e c S sv lv L hcall hih Cs st hst => (hc e c S sv lv L hcall hih Cs st hst).mono
    fun _ _ ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h1, h2, h3, h4, h5, h6.trans (by
        have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
        linarith), h7.trans (hX _)⟩

end Mono

/-- **`AsCompD` with the hand-over `ItHandB`** to the items, as `itS_asCompOK_of_runB` of the
general algorithm: the comparison phase also hands over the bounds on the lengths of the pair lists.
-/
theorem cm_asCompDB (I : Iface) (J : CostT) (Pg : Program) (F₀ F : Funs) (hst : GI.Cited.PointwiseStab)
    (hpre : GI.Cited.Preimage) (hm : GI.Cited.Membership) (H : AsHand)
    {fm b d stp tb jm jp : ℕ} (hset : CmSetAt Pg F hst hm fm b d stp tb jm jp)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHandB e c S L Cs st → H.items e c S L Cs st) :
    AsCompD I J Pg F₀ F H (cmRunX hst hpre hm) fm := by
  intro Ω C k e c S sv' lv L hcall hih Cs st hst'
  obtain ⟨hsub, Ag₀, hAg₀, hcl, sv, ps, fx, fy, logs, rfl, hcan, hps, hfx, hfy, hl1, hl2, hl3,
    hlogs⟩ := hc e c S L Cs st hst'
  refine (cm_runD I J Pg F₀ F hst hpre hm hset e c S sv' lv L hcall hih Cs Ag₀ hAg₀ hsub hcl sv ps
    fx fy logs hcan hps hfx hfy hl1 hl2 hl3 hlogs).mono ?_
  rintro w cost ⟨O, Ag, hAg, a, ex, rfl, hcost, hw⟩
  have hCs := hAg.1
  obtain ⟨-, hcert, htests, -⟩ := hAg
  refine ⟨Ag, hCs, a, ex, hi e c S L _ _ ⟨fun Ag' h => hsub h.1, Ag, ⟨hCs, rfl⟩,
    fun Ag' h' h1 h2 => ⟨hcl Ag' h' (h1.trans hcert), h2⟩, sv, ps, fx, fy, O, ?_, hcan, hps, ?_, ?_,
    hl1, hl2, hl3⟩, hcost, hw⟩
  · rw [← htests]
    exact cm_out_eqD ex sv ps fx fy
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]

/-! ### The round -/

/-- The list of the round of the general algorithm in `degProg`, in the form of `asAgg`. -/
theorem dp_hasAt_asAgg : (degProg h E D).HasAt asmAggBase (asAgg (rdF fagRdIdx) fcrE fcmE fitE
    (fagRest fcrF fcmF (fitF itHvHvIF (fc23F fc23ObF (fc10PrF fc11SojF)) (rcRepF fitRpIdx)))) :=
  dp_hasAt_agg

theorem dp_lcD : AsLcD (degProg h E D) degF GI.Proved.preimage GI.Proved.normalizedFactor
    (dgb 170) (abKrC GI.Proved.pointwiseStab) := by
  have hA := dp_hasAt_asAgg (h := h) (E := E) (D := D)
  have hlift : LiftAt (degProg h E D) 289 112 2 3 := asm_liftAt
  have hsb : ShiftAt (degProg h E D) 289 := ⟨hlift.shiftApp, hlift.append, hlift.addMap, hlift.addK⟩
  intro Ω C k Bc e c sv S hcan L con ps hps sel hsel cap os hos hcall
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, -, -, -, -, rfl⟩ := hcan.val
  exact lcMap_specD Bc GI.Proved.preimage GI.Proved.normalizedFactor (dg_blk 170 rfl)
    (dg_one 30 rfl) (as_blk hA 50 rfl) rfl (ab_krOK _ (as_blk hA 100 rfl) rfl)
    (abKrC_mono _) (as_one hA 7 rfl) hsb (as_blk hA 124 rfl) rfl (as_blk hA 120 rfl)
    (as_one hA 8 rfl) (as_blk hA 133 rfl) hcan con hps hsel cap os hos hcall

theorem dp_ceAt : AsCeAt (degProg h E D) GI.Proved.membership (asb 5) := by
  have hA := dp_hasAt_asAgg (h := h) (E := E) (D := D)
  exact asCeAt_of _ GI.Proved.membership (as_one hA 5 rfl) (as_blk hA 30 rfl) (as_blk hA 33 rfl)
    (as_one hA 9 rfl) (as_blk hA 42 rfl) (as_blk hA 136 rfl) (as_blk hA 30 rfl)
    (as_blk hA 36 rfl) rfl

/-- The parts of the round of the general algorithm in `degProg`. -/
theorem dp_fag_parts :
    let P := degProg h E D
    P.funs[asb 1]? = some (rdF fagRdIdx) ∧ P.funs[asb 2]? = some fcrE ∧
      P.funs[asb 3]? = some fcmE ∧ P.funs[asb 4]? = some fitE ∧ P.HasAt fagRdIdx fagRd ∧
      P.HasAt fagCrIdx fcrF ∧ P.HasAt fagCmIdx fcmF ∧
      P.HasAt fagItIdx (fitF itHvHvIF (fc23F fc23ObF (fc10PrF fc11SojF)) (rcRepF fitRpIdx)) :=
  fag_hasAt_parts ⟨fcr_fits, fcm_fits⟩ dp_hasAt_agg

theorem dp_certD (J : CostT) :
    AsCertD mI J (degProg h E D) asmF degF asHandImpl dpXw (dgb 21) := by
  obtain ⟨-, -, -, -, -, hcr, -, -⟩ := dp_fag_parts (h := h) (E := E) (D := D)
  obtain ⟨-, hstp, hfz, hmv⟩ := fcr_parts hcr
  exact asCertOK_ofD GI.Proved.pointwiseStab GI.Proved.preimage GI.Proved.membership mI J _ asmF
    degF asHandImpl dpXw (dg_one 21 rfl) (dg_one 24 rfl) hstp hmv hfz rfl rfl rfl
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h) fun W => by unfold dpXw; omega

theorem dp_compD (J : CostT) :
    AsCompD mI J (degProg h E D) asmF degF asHandImpl dpXw (dgb 22) := by
  obtain ⟨-, -, h3, -, -, -, hcm, -⟩ := dp_fag_parts (h := h) (E := E) (D := D)
  have m := fcm_setAt (F := asmF) (hst := GI.Proved.pointwiseStab) (hm := GI.Proved.membership)
    rfl h3 hcm rfl rfl
  have hset : CmSetAt (degProg h E D) degF GI.Proved.pointwiseStab GI.Proved.membership (dgb 22)
      (fagCmIdx + 100) (dgb 25) (fagCmIdx + 1) (fagCmIdx + 10) 1 0 :=
    ⟨dg_one 22 rfl, m.tup, dg_one 25 rfl, m.loop, m.mv, m.st, m.cl, m.hjm, m.hjp⟩
  have hc : AsCompD mI J (degProg h E D) asmF degF asHandImpl
      (cmRunX GI.Proved.pointwiseStab GI.Proved.preimage GI.Proved.membership) (dgb 22) :=
    cm_asCompDB mI J _ asmF degF GI.Proved.pointwiseStab GI.Proved.preimage
      GI.Proved.membership asHandImpl hset (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h)
  exact @AsCompD.mono mI J _ asmF degF asHandImpl _ dpXw (dgb 22) hc fun W => by
    unfold dpXw; omega

theorem dp_itemsD (J : CostT) :
    AsItemsD mI J (degProg h E D) asmF degF asHandImpl dpXw (dgb 23) := by
  obtain ⟨-, -, -, -, -, -, -, hit⟩ := dp_fag_parts (h := h) (E := E) (D := D)
  obtain ⟨hC', -, -, -⟩ := fit_hasAt_parts
    (rcR_fits itHvHvIF_fits (fc23_fits fc23ObF_length (fc10PrF_fits fc11SojF_length))) hit
  have m := fit_runAt hC'
  have hP : ItSRunAt (degProg h E D) degF (dgb 26) (fagItIdx + 2) (fagItIdx + 29) (dgb 27)
      (fagItIdx + 32) (fagItIdx + 33) (fagItIdx + 34) (fagItIdx + 35) (fagItIdx + 36)
      (fagItIdx + 30) (fagItIdx + 37) (fagItIdx + 172) (fagItIdx + 38) fitHvIdx fitC23Idx
      (fagItIdx + 39) (fagItIdx + 59) (fitC23Idx + 1) :=
    ⟨dg_one 26 rfl, m.hts, m.hdi0, m.hdb, dg_one 27 rfl, m.hloop, m.hmv⟩
  have hs := cProg_sub_degProg (h := h) (E := E) (D := D)
  have hih : IHAll mI (cProg mainGObjF fc11SojF) asmF := fun S => mR_ih .giant S
  obtain ⟨-, h1, h2, h3⟩ := mXc_spec
  have hi : AsItemsD mI J (degProg h E D) asmF degF asHandImpl (itSX mXs mXc) (dgb 23) :=
    itS_asItemsD mI J _ asmF degF asHandImpl (fun _ _ _ _ _ _ h => h)
      (dg_one 23 rfl) (ItSStrOK.of_sub hs hih mXs_spec.2) hP (ItSCaseOK.of_sub hs hih h1)
      (ItSCaseOK.of_sub hs hih h2) (ItSCaseOK.of_sub hs hih h3)
  exact @AsItemsD.mono mI J _ asmF degF asHandImpl _ dpXw (dgb 23) hi fun W => by
    unfold dpXw; omega

theorem dp_readOK : AsReadOK mI (degProg h E D) asmF asHandImpl dpXw (asb 1) :=
  rd_asReadOK_mono (AsReadOK.of_sub cProg_sub_degProg (fun S => mR_ih .giant S) mXr_spec.2)
    fun W => by unfold dpXw; omega

/-- **The code of `giantD`** in `degProg`. -/
noncomputable def dp_giantCode (Nm : ℕ) :
    GiantCode (dpCtx h E D mI Nm) asmF degF GI.Proved.preimage GI.Proved.normalizedFactor
      GI.Proved.membership (abKrC GI.Proved.pointwiseStab) dpXw where
  hcont := rfl
  fs := 0
  hsolve := rfl
  spec := fun J _ _ _ _ _ _ _ _ _ hcall hih hlcih =>
    as_agg_specD mI J GI.Proved.preimage GI.Proved.normalizedFactor GI.Proved.membership
      asHandImpl (dg_one 20 rfl) dp_readOK (dp_certD J) (dp_compD J) (dp_itemsD J) dp_lcD dp_ceAt
      hcall hih hlcih
  ih := fun S => dp_ih .giant S
  labW_le := fun _ _ => le_rfl

end GI.Degree
