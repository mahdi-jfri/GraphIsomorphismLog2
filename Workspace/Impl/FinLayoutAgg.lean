module

public import Workspace.Impl.FinLayoutCos
public import Workspace.Impl.RowReq
public import Workspace.Impl.GenSpecLayout
public import Workspace.Impl.AggSpecLayout
public import Workspace.Impl.AggReadOK
public import Workspace.Impl.AggCertHand
public import Workspace.Impl.AggItemStepSpec

@[expose] public section

/-!
# The aggregation round in the final program

`final_modulo_cos` leaves the hand-over data `AsHand` and the four phase contracts of the
aggregation round open. Here we fix the hand-over and the place of each phase in the program.

**The hand-over.** `asHandImpl` has the three relations of the phases:
`CpHand` (start of the certificate phase, `AggCertHand.lean`), `CmHand` (start of the
comparison phase, `AggCmpHand.lean`) and `ItHandB` (start of the items,
`AggItemStepSpec.lean`). `ItHandB` is `ItHand` with the lengths of the graph pairs `ps, fx, fy`
bounded by `(k + q)²`; without these bounds the start state of the items is not bounded by the
input weight. Their arguments are those of the fields of `AsHand`, so no
adapter is needed.

**The layout.** The list of the round is `fagAgg crE cmE itE crF cmF itF`, that is
`asAgg (rdF fagRdIdx) crE cmE itE (fagRest crF cmF itF)`. The entries `asb 2`, `asb 3`,
`asb 4` of the three unfinished phases are the parameters `crE`, `cmE`, `itE`; their helper
functions are the lists `crF`, `cmF`, `itF`. Offsets in `rest` (which starts at `asb 1000`):

| offset in `rest` | index | content | room |
|---|---|---|---|
| `0` | `fagRdIdx = asb 1000` | `rdFuns fagRdIdx 2` (the reading) | 151 of 1000 |
| `fagCrOff = 1000` | `fagCrIdx` | `crF` (the certificate phase) | 299000 |
| `fagCmOff = 300000` | `fagCmIdx` | `cmF` (the comparison phase) | 300000 |
| `fagItOff = 600000` | `fagItIdx` | `itF` (the items) | no bound (the list of the round is the last list of `asmProg`) |

The reading calls **Preimage** at primitive `2`, which is its place in `asmProg`.

**The bound.** The four phases share one bound in `AsSpec`. We take the sum
`fagX hpre Xc Xm Xi = rdX hpre + Xc + Xm + Xi` of the bound `rdX` of the reading and the bounds
of the other three, and move each contract to the sum (`fag_asCertOK_mono` and the like).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure)

set_option maxRecDepth 100000

/-! ### The hand-over -/

/-- **The hand-over relations of the aggregation round**: `CpHand`, `CmHand` and `ItHandB`. -/
def asHandImpl : AsHand where
  cert := fun e c S L Cs st => CpHand e c S L Cs st
  comp := fun e c S L Cs st => CmHand e c S L Cs st
  items := fun e c S L Cs st => ItHandB e c S L Cs st

/-! ### The layout -/

/-- The index of the module of the reading: the start of `rest`. -/
def fagRdIdx : ℕ := asb 1000

/-- The offset of the certificate phase in `rest`. -/
def fagCrOff : ℕ := 1000

/-- The offset of the comparison phase in `rest`. -/
def fagCmOff : ℕ := 300000

/-- The offset of the items in `rest`. -/
def fagItOff : ℕ := 600000

/-- The index of the helpers of the certificate phase. -/
def fagCrIdx : ℕ := asb (1000 + fagCrOff)

/-- The index of the helpers of the comparison phase. -/
def fagCmIdx : ℕ := asb (1000 + fagCmOff)

/-- The index of the helpers of the items. -/
def fagItIdx : ℕ := asb (1000 + fagItOff)

/-- The module of the reading, with **Preimage** at primitive `2`. -/
def fagRd : List Expr := rdFuns fagRdIdx 2

/-- **The helper list `rest` of the round**: the reading at offset `0`, then `crF`, `cmF`,
`itF` at their offsets. -/
def fagRest (crF cmF itF : List Expr) : List Expr :=
  asmPad fagCrOff fagRd ++ (asmPad (fagCmOff - fagCrOff) crF ++ (asmPad (fagItOff - fagCmOff) cmF ++
    itF))

/-- **The list of the aggregation round**: the reading `rdF fagRdIdx` at `asb 1`, the entries
`crE`, `cmE`, `itE` at `asb 2`, `asb 3`, `asb 4`, and `fagRest crF cmF itF` from `asb 1000`. -/
def fagAgg (crE cmE itE : Expr) (crF cmF itF : List Expr) : List Expr :=
  asAgg (rdF fagRdIdx) crE cmE itE (fagRest crF cmF itF)

/-- The room of the helper lists of the certificate and the comparison phase. -/
structure FagFits (crF cmF : List Expr) : Prop where
  hcr : crF.length ≤ fagCmOff - fagCrOff
  hcm : cmF.length ≤ fagItOff - fagCmOff

theorem length_fagRd : fagRd.length = 151 := rfl

theorem length_fagRd_le : fagRd.length ≤ fagCrOff := by
  rw [length_fagRd]; unfold fagCrOff; omega

private theorem fag_pad_left {P : Program} {b n : ℕ} {A B : List Expr}
    (h : P.HasAt b (asmPad n A ++ B)) : P.HasAt b A :=
  (show P.HasAt b (A ++ _) from h.left).left

private theorem fag_pad_right {P : Program} {b n : ℕ} {A B : List Expr} (hA : A.length ≤ n)
    (h : P.HasAt b (asmPad n A ++ B)) : P.HasAt (b + n) B := by
  simpa [length_asmPad hA] using h.right

/-- `rest` sits at `asb 1000` in the list of the round. -/
theorem fag_hasAt_rest {P : Program} {rd cr cm it : Expr} {rest : List Expr}
    (hG : P.HasAt asmAggBase (asAgg rd cr cm it rest)) : P.HasAt (asb 1000) rest := by
  obtain ⟨A, hA, hl⟩ : ∃ A : List Expr, asAgg rd cr cm it rest = A ++ rest ∧ A.length = 1000 := by
    refine ⟨_, rfl, ?_⟩
    simp only [List.length_append, List.length_replicate]
    rfl
  rw [hA] at hG
  simpa [asb, hl] using hG.right

set_option maxHeartbeats 4000000 in
/-- **The parts of the round** at their indices, from `HasAt` of the round at `asmAggBase`. -/
theorem fag_hasAt_parts {P : Program} {crE cmE itE : Expr} {crF cmF itF : List Expr}
    (hF : FagFits crF cmF) (hG : P.HasAt asmAggBase (fagAgg crE cmE itE crF cmF itF)) :
    P.funs[asb 1]? = some (rdF fagRdIdx) ∧ P.funs[asb 2]? = some crE ∧
      P.funs[asb 3]? = some cmE ∧ P.funs[asb 4]? = some itE ∧ P.HasAt fagRdIdx fagRd ∧
      P.HasAt fagCrIdx crF ∧ P.HasAt fagCmIdx cmF ∧ P.HasAt fagItIdx itF := by
  have h1 := fag_hasAt_rest hG
  have h2 := fag_pad_right length_fagRd_le h1
  have h3 := fag_pad_right hF.hcr h2
  have h4 := fag_pad_right hF.hcm h3
  have e2 : asb 1000 + fagCrOff = fagCrIdx := rfl
  have e3 : asb 1000 + fagCrOff + (fagCmOff - fagCrOff) = fagCmIdx := rfl
  have e4 : asb 1000 + fagCrOff + (fagCmOff - fagCrOff) + (fagItOff - fagCmOff) = fagItIdx := rfl
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  exact ⟨as_one hG 1 (by unfold asAgg; rfl), as_one hG 2 (by unfold asAgg; rfl),
    as_one hG 3 (by unfold asAgg; rfl), as_one hG 4 (by unfold asAgg; rfl),
    fag_pad_left h1, fag_pad_left h2, fag_pad_left h3, h4⟩

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
  {hder : DerivedSubgroup} {hni : NormalizedIntersection}
  {hnc : NormalClosure}
  {ext : List Prim} {recF labF jF : List Expr}

/-- **The final program** with the coset slot `flcCos recF labF jF` and the round
`fagAgg crE cmE itE crF cmF itF`. -/
noncomputable abbrev fagProg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection) (hnc : NormalClosure) (ext : List Prim)
    (recF labF jF : List Expr) (crE cmE itE : Expr) (crF cmF itF : List Expr) : Program :=
  flcProg hst hm hpre hfac hmb hO hC hder hni hnc ext gsGen recF labF jF
    (fagAgg crE cmE itE crF cmF itF)

/-- **The interface of the final program**, for the constants `Kl Dl Kj Dj Kc Dc` of the coset
program and the phase bound `X` of the round (the one of `final_modulo_cos`). -/
noncomputable abbrev fagIface (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hder : DerivedSubgroup)
    (hni : NormalizedIntersection) (hnc : NormalClosure) (Kl Dl Kj Dj Kc Dc : ℕ) (X : ℕ → ℕ) :
    Iface :=
  (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC)
    (rqWr hst hfac (rqAa hst hm hpre hfac (flRadK hder hni hm hpre hO)
      (flRadD hder hni hm hpre hO) (flcA hst hm hpre hO hder hni hnc Kl Dl Kj Dj Kc
        Dc))) (asWa hst hm hpre hfac X)).iface

theorem fag_row_le (hF : FlcFits recF labF jF) :
    (rlRow flRad (flCos (flcCos recF labF jF))).length ≤ asmSlot := by
  rw [length_rlRow length_flRad]
  have := length_flCos (length_flcCos hF)
  unfold rlCosOff asmSlot at *; omega

/-- **The parts of the round in the final program.** The last three are where the
certificate, comparison and items phases prove their contracts. -/
theorem fag_hasAt (hF : FlcFits recF labF jF) {crE cmE itE : Expr} {crF cmF itF : List Expr}
    (hA : FagFits crF cmF) :
    let P := fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF
      crE cmE itE crF cmF itF
    P.funs[asb 1]? = some (rdF fagRdIdx) ∧ P.funs[asb 2]? = some crE ∧
      P.funs[asb 3]? = some cmE ∧ P.funs[asb 4]? = some itE ∧ P.HasAt fagRdIdx fagRd ∧
      P.HasAt fagCrIdx crF ∧ P.HasAt fagCmIdx cmF ∧ P.HasAt fagItIdx itF :=
  fag_hasAt_parts hA (asmProg_hasAt_agg (by rw [length_gsGen]; unfold asmSlot; omega)
    (fag_row_le hF))

/-- The reading's primitive `2` is **Preimage** in the final program. -/
theorem fag_prim_pre {crE cmE itE : Expr} {crF cmF itF : List Expr} :
    (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF crE cmE itE
      crF cmF itF).prims[2]? = some (preimagePrim hpre) := rfl

end Asm

/-! ### Larger bounds -/

section Mono

variable {I : Iface} {Pg : Program} {F : Funs} {H : AsHand} {X X' : ℕ → ℕ} {f : ℕ}

/-- `AsCertOK` for a larger phase bound. -/
theorem fag_asCertOK_mono (h : AsCertOK I Pg F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsCertOK I Pg F H X' f :=
  fun e c S sv lv L hc Cs st hst => (h e c S sv lv L hc Cs st hst).mono
    fun _ _ ⟨Ag, hAg, a, ex, h1, h2, h3⟩ =>
      ⟨Ag, hAg, a, ex, h1, h2.trans (by
        have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
        linarith), h3.trans (hX _)⟩

/-- `AsCompOK` for a larger phase bound. -/
theorem fag_asCompOK_mono (h : AsCompOK I Pg F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsCompOK I Pg F H X' f :=
  fun e c S sv lv L hc Cs st hst => (h e c S sv lv L hc Cs st hst).mono
    fun _ _ ⟨Ag, hAg, a, ex, h1, h2, h3⟩ =>
      ⟨Ag, hAg, a, ex, h1, h2.trans (by
        have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
        linarith), h3.trans (hX _)⟩

/-- `AsItemsOK` for a larger phase bound. -/
theorem fag_asItemsOK_mono (h : AsItemsOK I Pg F H X f) (hX : ∀ W, X W ≤ X' W) :
    AsItemsOK I Pg F H X' f :=
  fun e c S sv lv L hc Cs st hst => (h e c S sv lv L hc Cs st hst).mono
    fun _ _ ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨Ag, hAg, pieces, os, ovs, pcs, ex, h1, h2, h3, h4, h5, h6.trans (by
        have : (X (I.inW .giant S) : ℝ) ≤ X' (I.inW .giant S) := by exact_mod_cast hX _
        linarith), h7.trans (hX _)⟩

end Mono

/-! ### The common bound -/

/-- **The phase bound of the round**: the sum of the bound `rdX` of the reading and the bounds
`Xc`, `Xm`, `Xi` of the certificate phase, the comparison phase and the items. -/
noncomputable def fagX (hpre : Preimage) (Xc Xm Xi : ℕ → ℕ) (W : ℕ) : ℕ :=
  rdX hpre W + Xc W + Xm W + Xi W

theorem fag_pbu (hpre : Preimage) {Xc Xm Xi : ℕ → ℕ} (hc : PBU fun _ W _ => Xc W)
    (hm : PBU fun _ W _ => Xm W) (hi : PBU fun _ W _ => Xi W) :
    PBU fun _ W _ => fagX hpre Xc Xm Xi W :=
  PBU.add (PBU.add (PBU.add (rd_pbu hpre) hc) hm) hi

theorem fag_le_rd (hpre : Preimage) (Xc Xm Xi : ℕ → ℕ) (W : ℕ) :
    rdX hpre W ≤ fagX hpre Xc Xm Xi W := by unfold fagX; omega

theorem fag_le_c (hpre : Preimage) (Xc Xm Xi : ℕ → ℕ) (W : ℕ) :
    Xc W ≤ fagX hpre Xc Xm Xi W := by unfold fagX; omega

theorem fag_le_m (hpre : Preimage) (Xc Xm Xi : ℕ → ℕ) (W : ℕ) :
    Xm W ≤ fagX hpre Xc Xm Xi W := by unfold fagX; omega

theorem fag_le_i (hpre : Preimage) (Xc Xm Xi : ℕ → ℕ) (W : ℕ) :
    Xi W ≤ fagX hpre Xc Xm Xi W := by unfold fagX; omega

/-! ### The reading in the final program -/

/-- **`AsReadOK` in the final program**, for the hand-over `asHandImpl` and any bound above
`rdX` (in particular `fagX`). The cited results enter through `rd_asReadOK`. -/
theorem fag_asReadOK
    (hK : GI.Cited.KaryCoherentRefinement)
    (hDl : GI.Cited.DesignLemma) {hst : PointwiseStab} {hm : Membership} {hpre : Preimage}
    {hfac : NormalizedFactor} {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
    {hder : DerivedSubgroup}
    {hni : NormalizedIntersection} {hnc : NormalClosure} {ext : List Prim}
    {recF labF jF : List Expr}
    (hF : FlcFits recF labF jF) {crE cmE itE : Expr} {crF cmF itF : List Expr}
    (hA : FagFits crF cmF) {Kl Dl Kj Dj Kc Dc : ℕ} {X X' : ℕ → ℕ}
    (hX : ∀ W, rdX hpre W ≤ X W) :
    AsReadOK (fagIface hst hm hpre hfac hmb hO hC hder hni hnc Kl Dl Kj Dj Kc Dc X')
      (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF crE cmE
        itE crF cmF itF) asmF asHandImpl X (asb 1) := by
  obtain ⟨h1, -, -, -, hrd, -⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (hmb := hmb) (hO := hO) (hC := hC) (hder := hder) (hni := hni)
    (hnc := hnc) (ext := ext) hF (crE := crE) (cmE := cmE) (itE := itE)
    (itF := itF) hA
  exact rd_asReadOK_mono (rd_asReadOK hpre hK hDl _ _ asmF h1 hrd fag_prim_pre
    (fun _ _ _ _ h => h) asHandImpl (fun _ _ _ _ _ _ h => h)) hX

end GI.Impl
