import Workspace.Impl.TermRad
import Workspace.Impl.RowLayout
import Workspace.Impl.GenSpecLayout

/-!
# The radical program T2 in the row slot `rad`

`flRadFuns b` is the code of T2 (the radical preimage, paragraph after Lemma A.21), written to
sit at index `b`. It is self-contained: besides the cited primitives it uses only its own
modules. Offsets from `b`:

* `0` the entry `radEntry`, `1` the step on one chief factor `radStepBody`;
* `2` the loop over the factors (`iterFuns`, 3 functions), `5` append (3), `8` `mkGroup` (7),
  `15` the subgroup test `le` (5). In all, 20 functions.

The primitive table of the final program is `[pst, mem, pre, fac] ++ gsExtra ++ flRadExtra ++
ext`. The list `flRadExtra` puts the four primitives of T2 that are not in the table yet at
indices `7`–`10`: **ChiefSeriesAlgo** `7`, **DerivedSubgroup** `8`, **QuotientCentralizer**
`9`, **NormalizedIntersection** `10`. **Membership** is the base primitive `1`.

`fl_radAt`: the layout `RadAt` holds at `rlb rlRadOff` in
`asmProg … (gsExtra … ++ (flRadExtra … ++ ext)) gen (rlRow (flRad) cos) agg`, for every `ext`,
`gen`, `cos` and `agg` that fit their slots. `fl_termRadSpec` is then `rad_termRadSpec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection)

set_option maxRecDepth 100000

/-- **The code of T2** at base `b`, with the primitive indices `jcs` (ChiefSeriesAlgo), `jder`
(DerivedSubgroup), `jqc` (QuotientCentralizer), `jni` (NormalizedIntersection), `jmem`
(Membership). -/
def flRadFuns (b jcs jder jqc jni jmem : ℕ) : List Expr :=
  [radEntry (b + 2) jcs jni, radStepBody (b + 5) (b + 8) (b + 15) jder jni jqc] ++
  iterFuns (b + 2) (b + 1) ++ appendFuns (b + 5) ++ mkGroupFuns (b + 8) ++ leFuns (b + 15) jmem

theorem length_flRadFuns (b jcs jder jqc jni jmem : ℕ) :
    (flRadFuns b jcs jder jqc jni jmem).length = 20 := rfl

/-- **The layout of T2** from the position of `flRadFuns` and the primitive entries. -/
theorem flRadAt_of {P : Program} {b jcs jder jqc jni jmem : ℕ} {hcs : ChiefSeriesAlgo}
    {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
    {hmem : Membership} (h : P.HasAt b (flRadFuns b jcs jder jqc jni jmem))
    (pc : P.prims[jcs]? = some (chiefSeriesPrim hcs))
    (pd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (pq : P.prims[jqc]? = some (quotientCentralizerPrim hqc))
    (pi : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pm : P.prims[jmem]? = some (membershipPrim hmem)) :
    RadAt P b (b + 2) (b + 1) (b + 5) (b + 8) (b + 15) jcs jder jni jqc jmem hcs hder hqc hni
      hmem where
  entry := by simpa using (h.block (gs := [radEntry (b + 2) jcs jni]) 0 rfl).single
  iter := h.block 2 rfl
  step :=
    { step := (h.block (gs := [radStepBody (b + 5) (b + 8) (b + 15) jder jni jqc]) 1 rfl).single
      ap := h.block 5 rfl
      mg := h.block 8 rfl
      le := h.block 15 rfl
      jd := pd
      jq := pq
      ji := pi
      jm := pm }
  jc := pc

/-- The four primitives of T2 that are not in `[pst, mem, pre, fac] ++ gsExtra`, at indices
`7`–`10` of the final table. -/
noncomputable def flRadExtra (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup)
    (hqc : QuotientCentralizer) (hni : NormalizedIntersection) : List Prim :=
  [chiefSeriesPrim hcs, derivedSubgroupPrim hder, quotientCentralizerPrim hqc,
    normalizedIntersectionPrim hni]

/-- The code of T2 in the row slot `rad`: base `rlb rlRadOff`, primitives `7`–`10` and `1`. -/
def flRad : List Expr := flRadFuns (rlb rlRadOff) 7 8 9 10 1

theorem length_flRad : flRad.length ≤ rlCosOff - rlRadOff := by
  rw [flRad, length_flRadFuns]; unfold rlCosOff rlRadOff; omega

/-- The constant of the cost bound of T2 (`radK` of the five cited primitives). -/
noncomputable def flRadK (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup)
    (hqc : QuotientCentralizer) (hni : NormalizedIntersection) (hm : Membership) : ℕ :=
  radK (chiefSeriesPrim hcs) (derivedSubgroupPrim hder) (quotientCentralizerPrim hqc)
    (normalizedIntersectionPrim hni) (membershipPrim hm)

/-- The exponent of the cost bound of T2 (`radD` of the five cited primitives). -/
noncomputable def flRadD (hcs : ChiefSeriesAlgo) (hder : DerivedSubgroup)
    (hqc : QuotientCentralizer) (hni : NormalizedIntersection) (hm : Membership) : ℕ :=
  radD (chiefSeriesPrim hcs) (derivedSubgroupPrim hder) (quotientCentralizerPrim hqc)
    (normalizedIntersectionPrim hni) (membershipPrim hm)

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {ext : List Prim} {gen cos agg : List Expr}

/-- **The layout `RadAt` of T2 in the final program.** -/
theorem fl_radAt (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ asmSlot - rlCosOff) :
    RadAt (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext))
        gen (rlRow flRad cos) agg)
      (rlb rlRadOff) (rlb rlRadOff + 2) (rlb rlRadOff + 1) (rlb rlRadOff + 5)
      (rlb rlRadOff + 8) (rlb rlRadOff + 15) 7 8 10 9 1 hcs hder hqc hni hm :=
  flRadAt_of (rl_hasAt_rad hg length_flRad hc) rfl rfl rfl rfl rfl

/-- **T2 in the final program**: `TermRadSpec` at `rlb rlRadOff` (`rad_termRadSpec`). -/
theorem fl_termRadSpec (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ asmSlot - rlCosOff) :
    Iface.TermRadSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ ext))
        gen (rlRow flRad cos) agg)
      (flRadK hcs hder hqc hni hm) (flRadD hcs hder hqc hni hm) (rlb rlRadOff) :=
  rad_termRadSpec (fl_radAt hg hc)

end Asm

end GI.Impl
