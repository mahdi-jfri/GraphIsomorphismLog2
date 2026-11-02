import Workspace.Impl.TermCosetCost
import Workspace.Impl.FinLayoutSup

/-!
# The coset program T4–T6 in the row slot `cos`

`tm_termCosetSpec` proves the contract of the coset program `tmCsTopF` from the specs of
its parts, each at an index parameter. Here we fix those indices in the final program.

`flcCoreFuns b rad sup rec lab jj jst` is the code of the coset program written to sit at index `b`. It calls
T2 at `rad`, T4 at `sup`, the A.20 recursion at `rec`, the label coset at `lab` and the
`J`-answer at `jj`. Offsets from `b`:

* single functions: `0` the entry `tmCsTopF`, `1` the residual program `tmCsResF`, `2` the type
  objects `tmCsObjsF`, `3`/`4` the two partner tests, `5`/`6` the `x`- and `y`-objects, `7` the
  first-position search, `8` the shift, `9` the fuel `ℓ`, `10` the table of the numbering,
  `11` one entry of the table, `12` the relabeling, `13` one conjugation;
* blocks: `14` `mkGroup` (7), `21` range (3), `24`/`27` the two `all` loops (3 each), `30`/`33`
  the two maps of objects (3 each), `36` append (3), `39` reduce (8), `47` inverse (12),
  `59` compose (4), `63` the map of shifts (3), `66` the restriction module `domFuns` (25),
  `91` the map of table entries (3), `94` the map of conjugations (3). In all, 97 functions.

The range and inverse modules are shared by the residual program and the table.

**The slot `cos`.** It is `flcCos recF labF jF`: the code of the coset program at offset `0`, the A.20
recursion `recF` at offset `flcRecOff = 1000`, the label coset `labF` at
`flcLabOff = 300000` and the `J`-answer `jF` at `flcJOff = 550000` (both for the abelian layer).
The three lists are parameters, so their finished programs can be dropped in later. Each has
room up to the next offset, and `jF` up to `flSupOff = 800000`, where T4 starts.

`flc_termCosetSpec`: `TermCosetSpec` at `rlb rlCosOff` in the final program, from the cited
`PointwiseStab` and `DixonDerivedLength` and the specs `TermRecSpec`, `TermGlueLabSpec`,
`TermJSpec` at `flcRecIdx`, `flcLabIdx`, `flcJIdx`. T2 and T4 come from `fl_termRadSpec` and
`fl_termSupSpec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure)

set_option maxRecDepth 100000

/-- The fourteen single functions of the coset program (offsets `0`–`13`). -/
def flcSingles (b rad sup rec lab jj : ℕ) : List Expr :=
  [tmCsTopF (b + 1) lab jj (b + 10) (b + 12),
    tmCsResF (b + 14) rad sup (b + 2) (b + 63) (b + 9) rec (b + 59) (b + 36) (b + 39),
    tmCsObjsF (b + 21) (b + 24) (b + 27) (b + 30) (b + 33),
    tmCsPxF (b + 7), tmCsPyF (b + 7),
    tmCsObjXF (b + 7) (b + 36) (b + 39) (b + 47), tmCsObjYF (b + 7) (b + 5) (b + 59),
    tmCsFirstF (b + 7), tmCsShF (b + 59), tmCsEllF (b + 9),
    tmCsTabF (b + 66) (b + 21) (b + 91) (b + 47), tmCsTabEF,
    tmCsRelF (b + 13) (b + 94), tmCsConjF (b + 59)]

/-- **The code of the coset program** at base `b`. It calls T2 at `rad`, T4 at `sup`, the A.20 recursion at
`rec`, the label coset at `lab`, the `J`-answer at `jj`, and PointwiseStab at primitive `jst`. -/
def flcCoreFuns (b rad sup rec lab jj jst : ℕ) : List Expr :=
  flcSingles b rad sup rec lab jj ++ (mkGroupFuns (b + 14) ++ (rangeFuns (b + 21) ++
  (allFuns (b + 24) (b + 3) ++ (allFuns (b + 27) (b + 4) ++ (mapFuns (b + 30) (b + 5) ++
  (mapFuns (b + 33) (b + 6) ++ (appendFuns (b + 36) ++ (redFuns (b + 39) jst ++
  (invFuns (b + 47) ++ (composeFuns (b + 59) ++ (mapFuns (b + 63) (b + 8) ++
  (domFuns (b + 66) ++ (mapFuns (b + 91) (b + 11) ++ mapFuns (b + 94) (b + 13))))))))))))))

theorem length_flcCoreFuns (b rad sup rec lab jj jst : ℕ) :
    (flcCoreFuns b rad sup rec lab jj jst).length = 97 := by
  have e1 : (flcSingles b rad sup rec lab jj).length = 14 := rfl
  have e2 : (mkGroupFuns (b + 14)).length = 7 := rfl
  have e3 : ∀ c, (rangeFuns c).length = 3 := fun _ => rfl
  have e4 : ∀ c d, (allFuns c d).length = 3 := fun _ _ => rfl
  have e5 : ∀ c d, (mapFuns c d).length = 3 := fun _ _ => rfl
  have e6 : (appendFuns (b + 36)).length = 3 := rfl
  have e7 : (redFuns (b + 39) jst).length = 8 := rfl
  have e8 : (invFuns (b + 47)).length = 12 := rfl
  have e9 : (composeFuns (b + 59)).length = 4 := rfl
  simp only [flcCoreFuns, List.length_append, e1, e2, e3, e4, e5, e6, e7, e8, e9, length_domFuns]

private theorem flc_right {P : Program} {b b' : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

/-- The modules of the coset program, one by one. -/
theorem flc_core_parts {P : Program} {b rad sup rec lab jj jst : ℕ}
    (h : P.HasAt b (flcCoreFuns b rad sup rec lab jj jst)) :
    P.HasAt b (flcSingles b rad sup rec lab jj) ∧ P.HasAt (b + 14) (mkGroupFuns (b + 14)) ∧
      P.HasAt (b + 21) (rangeFuns (b + 21)) ∧ P.HasAt (b + 24) (allFuns (b + 24) (b + 3)) ∧
      P.HasAt (b + 27) (allFuns (b + 27) (b + 4)) ∧ P.HasAt (b + 30) (mapFuns (b + 30) (b + 5)) ∧
      P.HasAt (b + 33) (mapFuns (b + 33) (b + 6)) ∧ P.HasAt (b + 36) (appendFuns (b + 36)) ∧
      P.HasAt (b + 39) (redFuns (b + 39) jst) ∧ P.HasAt (b + 47) (invFuns (b + 47)) ∧
      P.HasAt (b + 59) (composeFuns (b + 59)) ∧ P.HasAt (b + 63) (mapFuns (b + 63) (b + 8)) ∧
      P.HasAt (b + 66) (domFuns (b + 66)) ∧ P.HasAt (b + 91) (mapFuns (b + 91) (b + 11)) ∧
      P.HasAt (b + 94) (mapFuns (b + 94) (b + 13)) := by
  have h0 := flc_right h (b' := b + 14) rfl
  have h1 := flc_right h0 (b' := b + 21) rfl
  have h2 := flc_right h1 (b' := b + 24) rfl
  have h3 := flc_right h2 (b' := b + 27) rfl
  have h4 := flc_right h3 (b' := b + 30) rfl
  have h5 := flc_right h4 (b' := b + 33) rfl
  have h6 := flc_right h5 (b' := b + 36) rfl
  have h7 := flc_right h6 (b' := b + 39) rfl
  have h8 := flc_right h7 (b' := b + 47) rfl
  have h9 := flc_right h8 (b' := b + 59) rfl
  have h10 := flc_right h9 (b' := b + 63) rfl
  have h11 := flc_right h10 (b' := b + 66) rfl
  have h12 := flc_right h11 (b' := b + 91) (by rw [length_domFuns])
  have h13 := flc_right h12 (b' := b + 94) rfl
  exact ⟨h.left, h0.left, h1.left, h2.left, h3.left, h4.left, h5.left, h6.left, h7.left,
    h8.left, h9.left, h10.left, h11.left, h12.left, h13⟩

/-- **The layout of the coset program** from the position of `flcCoreFuns`. -/
theorem flcTopAt_of {P : Program} {b rad sup rec lab jj jst : ℕ}
    (h : P.HasAt b (flcCoreFuns b rad sup rec lab jj jst)) :
    TmCsTopAt P b (b + 1) lab jj (b + 10) (b + 12) (b + 14) rad sup (b + 2) (b + 63) (b + 8)
      (b + 9) rec (b + 59) (b + 36) (b + 39) jst (b + 21) (b + 24) (b + 3) (b + 27) (b + 4)
      (b + 30) (b + 5) (b + 33) (b + 6) (b + 7) (b + 47) (b + 66) (b + 21) (b + 91) (b + 11)
      (b + 47) (b + 13) (b + 94) := by
  obtain ⟨hs, hmkg, hrg, hax, hay, hmx, hmy, happ, hred, hinv, hcomp, hmsh, hdom, htb, hmp⟩ :=
    flc_core_parts h
  exact
  { hf := by simpa using (hs.block (gs := [tmCsTopF (b + 1) lab jj (b + 10) (b + 12)]) 0
      rfl).single
    hres :=
      { hf := (hs.block (gs := [tmCsResF (b + 14) rad sup (b + 2) (b + 63) (b + 9) rec (b + 59)
          (b + 36) (b + 39)]) 1 rfl).single
        hmkg := hmkg
        hobjs :=
          { hf := (hs.block (gs := [tmCsObjsF (b + 21) (b + 24) (b + 27) (b + 30) (b + 33)]) 2
              rfl).single
            hrg := hrg
            hax := hax
            hpx := (hs.block (gs := [tmCsPxF (b + 7)]) 3 rfl).single
            hay := hay
            hpy := (hs.block (gs := [tmCsPyF (b + 7)]) 4 rfl).single
            hmx := hmx
            hfx := (hs.block (gs := [tmCsObjXF (b + 7) (b + 36) (b + 39) (b + 47)]) 5 rfl).single
            hmy := hmy
            hfy := (hs.block (gs := [tmCsObjYF (b + 7) (b + 5) (b + 59)]) 6 rfl).single
            hfirst := (hs.block (gs := [tmCsFirstF (b + 7)]) 7 rfl).single
            happ := happ
            hred := hred
            hinv := hinv
            hcomp := hcomp }
        hmsh := hmsh
        hsh := (hs.block (gs := [tmCsShF (b + 59)]) 8 rfl).single
        hell := (hs.block (gs := [tmCsEllF (b + 9)]) 9 rfl).single
        hcomp := hcomp
        happ := happ
        hred := hred }
    htab :=
      { hf := (hs.block (gs := [tmCsTabF (b + 66) (b + 21) (b + 91) (b + 47)]) 10 rfl).single
        hdom := domAt_of_hasAt hdom
        hrg := hrg
        htb := htb
        htbe := (hs.block (gs := [tmCsTabEF]) 11 rfl).single
        hinv := hinv }
    hrel := (hs.block (gs := [tmCsRelF (b + 13) (b + 94)]) 12 rfl).single
    hconj := (hs.block (gs := [tmCsConjF (b + 59)]) 13 rfl).single
    hmp := hmp }

/-! ### The slot `cos` -/

/-- The offset of the A.20 recursion inside the slot `cos`. -/
def flcRecOff : ℕ := 1000

/-- The offset of the label coset (`TermGlueLabSpec`) inside the slot `cos`. -/
def flcLabOff : ℕ := 300000

/-- The offset of the `J`-answer (`TermJSpec`) inside the slot `cos`. -/
def flcJOff : ℕ := 550000

/-- The index of the A.20 recursion in the final program. -/
def flcRecIdx : ℕ := rlb (rlCosOff + flcRecOff)

/-- The index of the label coset in the final program. -/
def flcLabIdx : ℕ := rlb (rlCosOff + flcLabOff)

/-- The index of the `J`-answer in the final program. -/
def flcJIdx : ℕ := rlb (rlCosOff + flcJOff)

/-- The coset program at `rlb rlCosOff`, with T2 at `rlb rlRadOff`, T4 at `flSupIdx` and
PointwiseStab at primitive `0`. -/
def flcCore : List Expr :=
  flcCoreFuns (rlb rlCosOff) (rlb rlRadOff) flSupIdx flcRecIdx flcLabIdx flcJIdx 0

/-- **The slot `cos`** with the A.20 recursion `recF`, the label coset `labF` and the
`J`-answer `jF` at their fixed offsets. -/
def flcCos (recF labF jF : List Expr) : List Expr :=
  asmPad flcRecOff flcCore ++ (asmPad (flcLabOff - flcRecOff) recF ++
    (asmPad (flcJOff - flcLabOff) labF ++ jF))

/-- The room of each of the three lists. -/
structure FlcFits (recF labF jF : List Expr) : Prop where
  hrec : recF.length ≤ flcLabOff - flcRecOff
  hlab : labF.length ≤ flcJOff - flcLabOff
  hjj : jF.length ≤ flSupOff - flcJOff

theorem length_flcCore : flcCore.length ≤ flcRecOff := by
  rw [flcCore, length_flcCoreFuns]; unfold flcRecOff; omega

theorem length_flcCos {recF labF jF : List Expr} (hF : FlcFits recF labF jF) :
    (flcCos recF labF jF).length ≤ flSupOff := by
  have := hF.hjj
  simp only [flcCos, List.length_append, length_asmPad length_flcCore, length_asmPad hF.hrec,
    length_asmPad hF.hlab]
  unfold flcRecOff flcLabOff flcJOff flSupOff at *; omega

private theorem flc_pad_left {P : Program} {b n : ℕ} {A B : List Expr}
    (h : P.HasAt b (asmPad n A ++ B)) : P.HasAt b A :=
  (show P.HasAt b (A ++ _) from h.left).left

private theorem flc_pad_right {P : Program} {b n : ℕ} {A B : List Expr} (hA : A.length ≤ n)
    (h : P.HasAt b (asmPad n A ++ B)) : P.HasAt (b + n) B := by
  simpa [length_asmPad hA] using h.right

/-- The four parts of a `HasAt` of `flcCos` at `rlb rlCosOff`. -/
theorem flc_hasAt_parts {P : Program} {recF labF jF : List Expr} (hF : FlcFits recF labF jF)
    (h : P.HasAt (rlb rlCosOff) (flcCos recF labF jF)) :
    P.HasAt (rlb rlCosOff) flcCore ∧ P.HasAt flcRecIdx recF ∧ P.HasAt flcLabIdx labF ∧
      P.HasAt flcJIdx jF := by
  have h2 := flc_pad_right length_flcCore h
  have h3 := flc_pad_right hF.hrec h2
  have h4 := flc_pad_right hF.hlab h3
  have e2 : rlb rlCosOff + flcRecOff = flcRecIdx := by
    rfl
  have e3 : rlb rlCosOff + flcRecOff + (flcLabOff - flcRecOff) = flcLabIdx := by
    rfl
  have e4 : rlb rlCosOff + flcRecOff + (flcLabOff - flcRecOff) + (flcJOff - flcLabOff) =
      flcJIdx := by
    rfl
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  exact ⟨flc_pad_left h, flc_pad_left h2, flc_pad_left h3, h4⟩

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {hsy : SylowAlgo} {hsc : SylowConjugate} {hnc : NormalClosure}
  {ext : List Prim} {gen agg recF labF jF : List Expr}

/-- The final program with the slot `cos` filled by `flcCos recF labF jF`. -/
noncomputable abbrev flcProg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hsc : SylowConjugate)
    (hnc : NormalClosure) (ext : List Prim) (gen : List Expr) (recF labF jF agg : List Expr) :
    Program :=
  asmProg hst hm hpre hfac
    (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ (flSupExtra hsy hsc hnc ++ ext)))
    gen (rlRow flRad (flCos (flcCos recF labF jF))) agg

/-- The four parts of the slot `cos` sit at their indices in the final program. The last
three are where the later programs `recF`, `labF`, `jF` must prove their specs. -/
theorem flc_hasAt (hg : gen.length ≤ asmSlot) (hF : FlcFits recF labF jF) :
    let P := flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext gen recF labF
      jF agg
    P.HasAt (rlb rlCosOff) flcCore ∧ P.HasAt flcRecIdx recF ∧ P.HasAt flcLabIdx labF ∧
      P.HasAt flcJIdx jF :=
  flc_hasAt_parts hF (fl_hasAt_cos hg (length_flcCos hF))

/-- **The layout `TmCsTopAt` of the coset program in the final program.** -/
theorem flc_topAt (hg : gen.length ≤ asmSlot) (hF : FlcFits recF labF jF) :
    TmCsTopAt (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext gen recF labF
        jF agg)
      (rlb rlCosOff) (rlb rlCosOff + 1) flcLabIdx flcJIdx (rlb rlCosOff + 10)
      (rlb rlCosOff + 12) (rlb rlCosOff + 14) (rlb rlRadOff) flSupIdx (rlb rlCosOff + 2)
      (rlb rlCosOff + 63) (rlb rlCosOff + 8) (rlb rlCosOff + 9) flcRecIdx (rlb rlCosOff + 59)
      (rlb rlCosOff + 36) (rlb rlCosOff + 39) 0 (rlb rlCosOff + 21) (rlb rlCosOff + 24)
      (rlb rlCosOff + 3) (rlb rlCosOff + 27) (rlb rlCosOff + 4) (rlb rlCosOff + 30)
      (rlb rlCosOff + 5) (rlb rlCosOff + 33) (rlb rlCosOff + 6) (rlb rlCosOff + 7)
      (rlb rlCosOff + 47) (rlb rlCosOff + 66) (rlb rlCosOff + 21) (rlb rlCosOff + 91)
      (rlb rlCosOff + 11) (rlb rlCosOff + 47) (rlb rlCosOff + 13) (rlb rlCosOff + 94) :=
  flcTopAt_of (flc_hasAt (agg := agg) (ext := ext) hg hF).1

/-- The cost exponent of T4–T6 in the final program: `tmCsA` with the constants of T2
(`flRadK`, `flRadD`), of T4 (`supK`, `supD`) and the constants `Kl Dl` of the label coset,
`Kj Dj` of the `J`-answer and `Kc Dc` of the A.20 recursion. -/
noncomputable def flcA (hst : PointwiseStab) (hm : Membership) (hO : GroupOrder)
    (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup) (hqc : QuotientCentralizer)
    (hni : NormalizedIntersection) (hsy : SylowAlgo) (hsc : SylowConjugate) (hnc : NormalClosure)
    (Kl Dl Kj Dj Kc Dc : ℕ) : ℝ :=
  tmCsA (pointwiseStabPrim hst) (flRadK hcs hder hqc hni hm) (flRadD hcs hder hqc hni hm)
    (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))
    (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
      (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc)) Kl Dl Kj Dj Kc Dc

/-- **T4–T6 in the final program**: `TermCosetSpec` at `rlb rlCosOff` (`tm_termCosetSpec`),
from the specs of the A.20 recursion, the label coset and the `J`-answer at their fixed
indices. T2 and T4 are `fl_termRadSpec` and `fl_termSupSpec`. -/
theorem flc_termCosetSpec (dixon : GI.Cited.DixonDerivedLength) (hg : gen.length ≤ asmSlot)
    (hF : FlcFits recF labF jF) {Kl Dl Kj Dj Kc Dc : ℕ}
    (hrec : Iface.TermRecSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc
      ext gen recF labF jF agg) Kc Dc flcRecIdx)
    (hlab : Iface.TermGlueLabSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc
      hnc ext gen recF labF jF agg) Kl Dl flcLabIdx)
    (hjj : Iface.TermJSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext
      gen recF labF jF agg) Kj Dj flcJIdx) :
    Iface.TermCosetSpec (flcProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext gen
        recF labF jF agg)
      (flcA hst hm hO hcs hder hqc hni hsy hsc hnc Kl Dl Kj Dj Kc Dc) (rlb rlCosOff) :=
  tm_termCosetSpec hst dixon (flc_topAt hg hF) rfl
    (fl_termRadSpec hg (length_flCos (length_flcCos hF)))
    (fl_termSupSpec hg (length_flcCos hF)) hrec hlab hjj

end Asm

end GI.Impl
