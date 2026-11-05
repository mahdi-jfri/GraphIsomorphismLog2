module

public import Workspace.Impl.FinLayoutItems
public import Workspace.Impl.FinLayoutCmp
public import Workspace.Impl.FinLayoutCertPrims

@[expose] public section

/-!
# The items in the final program

`fitConc c` (`FinLayoutItems.lean`) holds the programs of the items that are written. Here we
first prove their contracts from the entries `FitAt P c`, for any program `P` and base `c`:

* `fit_strOK`: the structure step at `c` meets `ItSStrOK` (`itS_strOK`), given the refinement at
  primitive `19`, **PointwiseStab** at `0` and **GroupOrder** at `5`;
* `fit_runAt`: the run meets `ItSRunAt`;
* `fit_c1`: Case 1 meets `ItSCaseOK` (`itS_c1_caseOK`);
* `fit_c2a`: Case 2a meets `ItSCaseOK` from the contract `ItHvInitOK` of its init program
  (`itS_c2a_caseOK`);
* `fit_rcCertSpec`: the certificate search meets `RcCertSpec` (`rc_cert_spec`).

Then we fix the items' list of the final program, `fitF hvIF c23F rpF` at `fagItIdx`, and its
entry `fitE` at `asb 4`:

| offset in `fitF` | index | content | room |
|---|---|---|---|
| `0` | `fagItIdx` | `fitConc fagItIdx` (298 functions) | `10000` |
| `fitHvOff = 10000` | `fitHvIdx` | `hvIF`: the init program of Case 2a (entry at offset `0`) | `90000` |
| `fitC23Off = 100000` | `fitC23Idx` | `c23F`: Cases 2b and 3 (init at offset `0`, branch step at `1`) | `200000` |
| `fitRpOff = 300000` | `fitRpIdx` | `rpF`: the rectangle representation program (entry at offset `0`) | `100000` |

The three lists `hvIF`, `c23F`, `rpF` are not written yet; they are parameters with length
bounds (`FitFits`). The certificate search `rcCertF` sits at `fitRcIdx = fagItIdx + 61`, where
the programs of Cases 2b and 3 can call it (`fit_rcCertSpec_final`).

`fit_asItemsOK` is `AsItemsOK` in the final program, for every interface, from the two open
contracts: `ItHvInitOK` at `fitHvIdx` and the contract `ItSCaseOK` of Cases 2b and 3 at
`fitC23Idx`, `fitC23Idx + 1`. Its bound is `fitXi = itSX (itSXs …) fitXc`, where
`fitXc = itSC1X + itHvX Xh + X3` is the sum of the bounds of the three case contracts.
`fit_Xi_pbu`: this bound is polynomial when `Xh` and `X3` are.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure SolvableCosetIntersection HermiteFullRank
  SmithNonsingular ConstructiveMembership VectorStabilizer KaryRefinement)

set_option maxRecDepth 100000

/-! ### The contracts from the entries -/

section Entries

variable {P : Program} {c : ℕ}

/-- The indices of the Case 1 item in `fitConc c`. -/
def fitC1Idx (c : ℕ) : ItC1Idx where
  f := c + 40
  dat := c + 41
  chk := c + 45
  fnd := c + 223
  ft := c + 47
  swt := c + 226
  sb := c + 48
  gen := c + 49
  sch := c + 53
  cmp := c + 241
  par := c + 55
  rng := c + 74
  mpS := c + 199
  sz := c + 42
  cnt := c + 153
  mpP := c + 202
  pb := c + 43
  flt := c + 205
  kb := c + 44
  inv := c + 208
  al := c + 220
  ct := c + 46
  mpT := c + 229
  trB := c + 50
  mpG := c + 232
  gb := c + 51
  bs := c + 235
  bb := c + 52
  app := c + 172
  mpS' := c + 238
  sb' := c + 54
  mpI := c + 245
  ib := c + 56
  fltI := c + 248
  it := c + 57
  fld := c + 251
  st := c + 58

/-- **The structure step meets `ItSStrOK`** at `c`, with the bound `itSXs`. The cited tasks enter
through the primitives `19` (`KaryRefinement P₀.κ`), `0` (**PointwiseStab**) and `5`
(**GroupOrder**). -/
theorem fit_strOK (hA : FitAt P c) (hk : KaryRefinement P₀.κ) (hst : PointwiseStab)
    (hO : GroupOrder) (hjk : P.prims[19]? = some (karyRefinementPrim hk))
    (hjp : P.prims[0]? = some (pointwiseStabPrim hst))
    (hjo : P.prims[5]? = some (groupOrderPrim hO)) (I : Iface) (F : Funs) :
    ItSStrOK I P F (c + 0) (itSXs hk hst hO) := by
  have hacp : ItCaseOK P (c + 6) hst hO := itCaseOK_of hst hO hA.acp hA.orb hA.rb hA.fd hA.pd
    hA.fs hA.ps hA.cnt hA.g hA.pst hjp hA.fac hjo
  have hspl : StDSplitOK P (c + 20) := stDSplit_ok hA.spl hA.fdd hA.dv hA.dvv hA.cnt hA.frr
    hA.rf hA.add hA.df hA.rb hA.cf hA.h
  have hht : StDHitOK P (c + 18) := stDHit_ok hA.ht hA.h2 hA.ad hA.dv hA.dvv hA.cnt hA.rb hspl
    hA.vm hA.mb hA.vf hA.cf hA.h
  have hdes : StDesOK P (c + 17) := stDes_ok hA.des hA.fh hht hA.rb hA.vm hA.mb hA.vf hA.cf hA.h
    hA.ad hA.dv hA.dvv hA.cnt
  -- (`@`: otherwise Lean fills the implicit binders of the conclusion `ItSStrOK` with
  -- metavariables)
  exact @itS_strOK hk hst hO I P F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hA.str hA.col hA.ts hA.pw hA.rb hA.mp hA.tv hA.dc hA.bc hA.brel hA.fr hA.brep hjk hA.cse hacp
    hA.grp hA.mpsf hA.sf hA.app hA.sp hA.dom hA.orb hA.fd hA.pd hA.cnt hA.s2b hA.brep hA.s3
    hA.fs3 hA.spp hdes

/-- **The programs of the run** at their indices in `fitConc c`; the init programs of Cases 2a
and 2b/3 are at `c + fitHvOff` and `c + fitC23Off`, the branch step of Cases 2b/3 at
`c + (fitC23Off + 1)`. -/
theorem fit_runAt (hA : FitAt P c) :
    ItSRunAt P asmF (c + 28) (c + 2) (c + 29) (c + 31) (c + 32) (c + 33) (c + 34) (c + 35) (c + 36)
      (c + 30) (c + 37) (c + 172) (c + 38) (c + fitHvOff) (c + fitC23Off) (c + 39) (c + 59)
      (c + (fitC23Off + 1)) :=
  ⟨hA.run, itS_ts_of hA.ts hA.pw hA.rb hA.mp hA.tv hA.dc, hA.di0, hA.db, hA.drun, hA.dloop,
    ⟨hA.mv, hA.m0, hA.m1, hA.m3, hA.facc, hA.app⟩⟩

/-- **Case 1 meets its contract** in `fitConc c`, with the bound `itSC1X`. -/
theorem fit_c1 (hA : FitAt P c) (I : Iface) (F : Funs) :
    ItSCaseOK I P F (· = .one) (c + 38) (c + 39) itSC1X :=
  itS_c1_caseOK I (IC := fitC1Idx c) hA.i1 hA.b1 hA.grp hA.rb hA.mpsf hA.sf hA.app hA.orb
    ⟨hA.c1, hA.rb, hA.dat, hA.mpS, hA.sz, hA.cnt, hA.mpP, hA.pb, hA.flt, hA.kb, hA.inv, hA.chk,
      hA.al, hA.ct, hA.fnd, hA.ft, hA.swt, hA.sb, hA.gen, hA.mpT, hA.trB, hA.mpG, hA.gb, hA.bs,
      hA.bb, hA.app, hA.sch, hA.mpS2, hA.sb2, hA.cmp, hA.par, hA.mpI, hA.ib, hA.fltI, hA.it,
      hA.fld, hA.st⟩

/-- **Case 2a meets its contract** in `fitConc c`, for an init program at `f0` that meets
`ItHvInitOK` with the bound `Xh`. -/
theorem fit_c2a (hA : FitAt P c) (I : Iface) (F : Funs) {f0 : ℕ} {Xh : ℕ → ℕ}
    (hinit : ItHvInitOK I P F f0 Xh) : ItSCaseOK I P F (· = .twoA) f0 (c + 59) (itHvX Xh) :=
  itS_c2a_caseOK I P hinit hA.b2 hA.pc hA.cmp hA.app

/-- The function table of the certificate search in `fitConc c`. -/
theorem fit_rcCertOk (hA : FitAt P c) :
    RcCertOk P (c + 61) (c + 254) (c + 62) (c + 257) (c + 63) (c + 260) (c + 264) (c + 268)
      (c + 64) (c + 271) (c + 65) (c + 74) (c + 274) (c + 66) (c + 277) (c + 67) (c + 280)
      (c + 283) (c + 289) (c + 153) (c + 68) (c + 286) (c + 69) (c + 70) (c + 292) (c + 295) :=
  ⟨⟨hA.cand, hA.flt3, hA.et, hA.rb, hA.mb2, hA.br, hA.mbe, hA.cond, hA.mc, hA.cnt, hA.mcd, hA.cd,
      hA.mg, hA.gt, hA.al2, hA.tw, hA.fe, hA.en⟩,
    hA.rc, hA.flt2, hA.dg, hA.md, hA.dr, hA.gth, hA.fq, hA.fnd2⟩

/-- **The certificate search meets `RcCertSpec`** at `c + 61`, with the bound `rcCertB`. -/
theorem fit_rcCertSpec (hA : FitAt P c) : RcCertSpec P (c + 61) rcCertB :=
  rc_cert_spec (fit_rcCertOk hA)

end Entries

/-! ### The bounds -/

/-- **The bound of Case 2a is polynomial** when the bound `Xh` of its init program is. -/
theorem fit_hvX_pbu {Xh : ℕ → ℕ} (hXh : PBU fun _ W _ => Xh W) :
    PBU fun _ W _ => itHvX Xh W := by
  have h1 : PBU fun _ W _ => itHvBu W + itSVB W + 5 * (2 * W + 3 + 1) ^ 2 := by
    simp only [itHvBu, itSVB, cmOutB, cmPb, cmNb]
    norm_poly
  have hR : PBU fun _ W _ => itHvRB Xh W :=
    (PBU.addc (PBU.smul 100 (PBU.add hXh h1)) 100).mono fun _ W _ => by
      unfold itHvRB; omega
  have hP : PBU fun _ _ B => itHvB3C B (itHvPcC B) + itHvBC B + B + 10 := by
    simp only [itHvB3C, itHvPcC, itHvBC]
    norm_poly
  have h2 := itS_pbu_subst (P := fun _ B => itHvB3C B (itHvPcC B) + itHvBC B + B + 10) hP hR
  exact (PBU.add hXh h2).mono fun _ W _ => by
    unfold itHvX; omega

/-- **The common bound of the three case contracts**: Case 1, Case 2a (for the bound `Xh` of
its init program) and Cases 2b and 3 (bound `X3`). -/
def fitXc (Xh X3 : ℕ → ℕ) (W : ℕ) : ℕ := itSC1X W + itHvX Xh W + X3 W

/-- **The bound of the items**: `itSX` of the bound of the structure step and `fitXc`. -/
noncomputable def fitXi (hk : KaryRefinement P₀.κ) (hst : PointwiseStab) (hO : GroupOrder)
    (Xh X3 : ℕ → ℕ) : ℕ → ℕ :=
  itSX (itSXs hk hst hO) (fitXc Xh X3)

theorem fit_Xi_pbu (hk : KaryRefinement P₀.κ) (hst : PointwiseStab) (hO : GroupOrder)
    {Xh X3 : ℕ → ℕ} (hXh : PBU fun _ W _ => Xh W) (hX3 : PBU fun _ W _ => X3 W) :
    PBU fun _ W _ => fitXi hk hst hO Xh X3 W :=
  itS_X_pbu (itS_Xs_pbu hk hst hO)
    ((PBU.add (PBU.add itS_sc1X_pbu (fit_hvX_pbu hXh)) hX3).mono fun _ _ _ => le_of_eq rfl)

/-! ### The items' list of the final program -/

/-- The index of the init program of Case 2a. -/
def fitHvIdx : ℕ := fagItIdx + fitHvOff

/-- The index of the init program of Cases 2b and 3; their branch step is at `fitC23Idx + 1`. -/
def fitC23Idx : ℕ := fagItIdx + fitC23Off

/-- The index of the rectangle representation program. -/
def fitRpIdx : ℕ := fagItIdx + fitRpOff

/-- The index of the certificate search `rcCertF`. -/
def fitRcIdx : ℕ := fagItIdx + 61

/-- **The entry of the items** at `asb 4`: the structure step at `fagItIdx`, then the run at
`fagItIdx + 28`. -/
def fitE : Expr := itSItemsF (fagItIdx + 0) (fagItIdx + 28)

/-- **The items' list of the final program** (see the module docstring). -/
noncomputable def fitF (hvIF c23F rpF : List Expr) : List Expr :=
  asmPad fitHvOff (fitConc fagItIdx) ++ (asmPad (fitC23Off - fitHvOff) hvIF ++
    (asmPad (fitRpOff - fitC23Off) c23F ++ rpF))

/-- The room of the three lists that are not written yet. -/
structure FitFits (hvIF c23F rpF : List Expr) : Prop where
  hhv : hvIF.length ≤ fitC23Off - fitHvOff
  hc23 : c23F.length ≤ fitRpOff - fitC23Off
  hrp : rpF.length ≤ fitRoom - fitRpOff

/-- **The items' list fits its room** of `fitRoom` functions. -/
theorem fit_fits {hvIF c23F rpF : List Expr} (h : FitFits hvIF c23F rpF) :
    (fitF hvIF c23F rpF).length ≤ fitRoom := by
  unfold fitF
  simp only [List.length_append, length_asmPad (length_fitConc_le fagItIdx), length_asmPad h.hhv,
    length_asmPad h.hc23]
  have := h.hrp
  unfold fitRoom fitRpOff fitC23Off fitHvOff at *
  omega

/-- **The parts of the items' list** at their indices. -/
theorem fit_hasAt_parts {P : Program} {hvIF c23F rpF : List Expr} (hF : FitFits hvIF c23F rpF)
    (h : P.HasAt fagItIdx (fitF hvIF c23F rpF)) :
    FitAt P fagItIdx ∧ P.HasAt fitHvIdx hvIF ∧ P.HasAt fitC23Idx c23F ∧ P.HasAt fitRpIdx rpF := by
  unfold fitF at h
  have h1 := h.left.left
  have h2 : P.HasAt (fagItIdx + fitHvOff)
      (asmPad (fitC23Off - fitHvOff) hvIF ++ (asmPad (fitRpOff - fitC23Off) c23F ++ rpF)) := by
    simpa [length_asmPad (length_fitConc_le fagItIdx)] using h.right
  have h3 : P.HasAt (fagItIdx + fitHvOff + (fitC23Off - fitHvOff))
      (asmPad (fitRpOff - fitC23Off) c23F ++ rpF) := by
    simpa [length_asmPad hF.hhv] using h2.right
  have h4 : P.HasAt (fagItIdx + fitHvOff + (fitC23Off - fitHvOff) + (fitRpOff - fitC23Off))
      rpF := by
    simpa [length_asmPad hF.hc23] using h3.right
  have e3 : fagItIdx + fitHvOff + (fitC23Off - fitHvOff) = fitC23Idx := rfl
  have e4 : fagItIdx + fitHvOff + (fitC23Off - fitHvOff) + (fitRpOff - fitC23Off) = fitRpIdx := rfl
  rw [e3] at h3
  rw [e4] at h4
  exact ⟨fit_at h1, h2.left.left, h3.left.left, h4⟩

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
  {hder : DerivedSubgroup} {hni : NormalizedIntersection}
  {hnc : NormalClosure}
  {hs : SolvableCosetIntersection} {hh : HermiteFullRank} {hn : SmithNonsingular}
  {hcmb : ConstructiveMembership} {hv : VectorStabilizer} {ext'' : List Prim}
  {recF labF jF : List Expr}

/-- **The certificate search in the final program** meets `RcCertSpec` at `fitRcIdx`. -/
theorem fit_rcCertSpec_final (hk : KaryRefinement P₀.κ) (hF : FlcFits recF labF jF)
    {crE cmE : Expr} {crF cmF : List Expr} (hA : FagFits crF cmF) {hvIF c23F rpF : List Expr}
    (hfit : FitFits hvIF c23F rpF) :
    RcCertSpec (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF hvIF c23F rpF)) fitRcIdx rcCertB := by
  obtain ⟨-, -, -, -, -, -, -, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) hF (crE := crE) (cmE := cmE)
    (itE := fitE) (itF := fitF hvIF c23F rpF) hA
  exact fit_rcCertSpec (fit_hasAt_parts hfit hit).1

/-- **The items in the final program.** For every interface `I`, the entry `fitE` at `asb 4`
with the list `fitF hvIF c23F rpF` at `fagItIdx` meets `AsItemsOK` for the hand-over
`asHandImpl` and the bound `fitXi`, given the two open contracts: `ItHvInitOK` of the init
program of Case 2a at `fitHvIdx` (bound `Xh`) and `ItSCaseOK` of Cases 2b and 3 at `fitC23Idx`,
`fitC23Idx + 1` (bound `X3`). The cited tasks enter through the primitives `19`, `0` and `5`
(`fit_strOK`). -/
theorem fit_asItemsOK (hk : KaryRefinement P₀.κ) (hF : FlcFits recF labF jF)
    {crE cmE : Expr} {crF cmF : List Expr} (hA : FagFits crF cmF) {hvIF c23F rpF : List Expr}
    (hfit : FitFits hvIF c23F rpF) (I : Iface) {Xh X3 : ℕ → ℕ}
    (hinit : ItHvInitOK I (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF hvIF c23F rpF)) asmF fitHvIdx Xh)
    (h3 : ItSCaseOK I (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF hvIF c23F rpF)) asmF (fun a => a = .twoB ∨ a = .three) fitC23Idx (fitC23Idx + 1) X3) :
    AsItemsOK I (fagProg hst hm hpre hfac hmb hO hC hder hni hnc
      (linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) recF labF jF crE cmE fitE crF cmF
      (fitF hvIF c23F rpF)) asmF asHandImpl (fitXi hk hst hO Xh X3) (asb 4) := by
  obtain ⟨-, -, -, h4, -, -, -, hit⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc)
    (ext := linA20Extra hs hh hn hcmb hv ++ (aggExtra hk ++ ext'')) hF (crE := crE) (cmE := cmE)
    (itE := fitE) (itF := fitF hvIF c23F rpF) hA
  obtain ⟨hC', -, -, -⟩ := fit_hasAt_parts hfit hit
  -- the three case contracts, each raised to the common bound `fitXc`
  have h1 := ItSCaseOK.mono I _ (fit_c1 hC' I asmF) (Xc' := fitXc Xh X3)
    fun W => by unfold fitXc; omega
  have h2 := ItSCaseOK.mono I _ (fit_c2a hC' I asmF hinit) (Xc' := fitXc Xh X3)
    fun W => by unfold fitXc; omega
  have h3' := ItSCaseOK.mono I _ h3 (Xc' := fitXc Xh X3) fun W => by unfold fitXc; omega
  -- `asHandImpl` hands over `ItHandB` to the items
  unfold fitXi
  -- (`@`: otherwise Lean fills the implicit binders of the conclusion `AsItemsOK` with
  -- metavariables)
  exact @itS_asItemsOK I _ asmF asHandImpl (fun _ _ _ _ _ _ h => h)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h4 _ _
    (fit_strOK hC' hk hst hO fcr_prim_kary rfl rfl I asmF) (fit_runAt hC') h1 h2 h3'

end Asm

end GI.Impl
