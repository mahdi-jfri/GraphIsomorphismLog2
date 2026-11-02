import Workspace.Impl.TermSup
import Workspace.Impl.FinLayoutRad

/-!
# The solvable supplement T4 inside the coset slot `cos`

`flSupFuns b …` is the code of T4 (the solvable supplement, Lemma A.19), written to sit at
index `b`. It is self-contained: besides the cited primitives it uses only its own modules.
Offsets from `b`:

* single functions: `0` the entry `supEntry`, `1` one descent `supDescBody`, `2` the search
  `supFindBody`, `3` one search step `supSearchBody`, `4` one correction `supFixF`, `5` one
  conjugation `supConjF`;
* blocks: `6` the loop of descents (`iterFuns`), `9` the map of corrections, `12` `mkGroup`,
  `19` the loop of the search, `22` the subgroup test `le`, `27` inverse, `39` the map of
  conjugations, `42` compose. In all, 46 functions.

**Placement.** The code of T4–T6 goes in the row slot `cos`, at
`rlb rlCosOff`. We reserve the offset `flSupOff = 800000` inside that slot for T4: the slot is
`flCos cos = asmPad flSupOff cos ++ flSup`, so the code `cos` of T4–T6 may have up to `800000`
functions, and T4 sits at `rlb (rlCosOff + flSupOff)` (`flSupIdx`).

**Primitives.** NormalizedIntersection `10` (in `flRadExtra`), SylowAlgo `11`, SylowConjugate
`12`, NormalClosure `13` (in `flSupExtra`), GroupOrder `5` (in `gsExtra`), Membership `1`.

`fl_supAt`: the layout `SupAt` at `flSupIdx` in the final program, for every `cos` that fits;
`fl_termSupSpec` is then `sup_termSupSpec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure)

set_option maxRecDepth 100000

/-- **The code of T4** at base `b`, with the primitive indices `jni` (NormalizedIntersection),
`jsy` (SylowAlgo), `jnc` (NormalClosure), `jord` (GroupOrder), `jm` (Membership), `jsc`
(SylowConjugate). -/
def flSupFuns (b jni jsy jnc jord jm jsc : ℕ) : List Expr :=
  [supEntry (b + 6) jni, supDescBody (b + 12) jni (b + 2) (b + 9), supFindBody (b + 19) jord,
    supSearchBody (b + 12) (b + 22) jsy jnc jord, supFixF (b + 27) (b + 39) (b + 42) jsc,
    supConjF (b + 42)] ++
  iterFuns (b + 6) (b + 1) ++ mapFuns (b + 9) (b + 4) ++ mkGroupFuns (b + 12) ++
  iterFuns (b + 19) (b + 3) ++ leFuns (b + 22) jm ++ invFuns (b + 27) ++ mapFuns (b + 39) (b + 5) ++
  composeFuns (b + 42)

theorem length_flSupFuns (b jni jsy jnc jord jm jsc : ℕ) :
    (flSupFuns b jni jsy jnc jord jm jsc).length = 46 := rfl

/-- **The layout of T4** from the position of `flSupFuns` and the primitive entries. -/
theorem flSupAt_of {P : Program} {b jni jsy jnc jord jm jsc : ℕ} {hni : NormalizedIntersection}
    {hsy : SylowAlgo} {hnc : NormalClosure} {hord : GroupOrder} {hmem : Membership}
    {hsc : SylowConjugate} (h : P.HasAt b (flSupFuns b jni jsy jnc jord jm jsc))
    (pni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (psy : P.prims[jsy]? = some (sylowPrim hsy))
    (pnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (pord : P.prims[jord]? = some (groupOrderPrim hord))
    (pm : P.prims[jm]? = some (membershipPrim hmem))
    (psc : P.prims[jsc]? = some (sylowConjugatePrim hsc)) :
    SupAt P b (b + 6) (b + 1) (b + 12) jni (b + 2) (b + 9) (b + 4) (b + 19) (b + 3) (b + 22) jsy
      jnc jord jm (b + 27) (b + 39) (b + 5) (b + 42) jsc hni hsy hnc hord hmem hsc where
  entry := by simpa using (h.block (gs := [supEntry (b + 6) jni]) 0 rfl).single
  iter := h.block 6 rfl
  desc :=
    { step := (h.block (gs := [supDescBody (b + 12) jni (b + 2) (b + 9)]) 1 rfl).single
      ni := pni
      find :=
        { entry := (h.block (gs := [supFindBody (b + 19) jord]) 2 rfl).single
          iter := h.block 19 rfl
          step :=
            { step := (h.block (gs := [supSearchBody (b + 12) (b + 22) jsy jnc jord]) 3
                rfl).single
              mg := h.block 12 rfl
              le := h.block 22 rfl
              sy := psy
              nc := pnc
              ord := pord
              mem := pm } }
      map := h.block 9 rfl
      fix :=
        { fix := (h.block (gs := [supFixF (b + 27) (b + 39) (b + 42) jsc]) 4 rfl).single
          inv := h.block 27 rfl
          map := h.block 39 rfl
          conj := (h.block (gs := [supConjF (b + 42)]) 5 rfl).single
          comp := h.block 42 rfl
          sc := psc } }

/-- The primitives of T4 that are not in the table yet, at indices `11`–`13` of the final
table: SylowAlgo `11`, SylowConjugate `12`, NormalClosure `13`. -/
noncomputable def flSupExtra (hsy : SylowAlgo) (hsc : SylowConjugate) (hnc : NormalClosure) :
    List Prim :=
  [sylowPrim hsy, sylowConjugatePrim hsc, normalClosurePrim hnc]

/-- The offset of T4 inside the coset slot `cos`. -/
def flSupOff : ℕ := 800000

/-- The index of T4 in the final program. -/
def flSupIdx : ℕ := rlb (rlCosOff + flSupOff)

/-- The code of T4 at `flSupIdx`, with the primitives `10, 11, 13, 5, 1, 12`. -/
def flSup : List Expr := flSupFuns flSupIdx 10 11 13 5 1 12

/-- **The coset slot** with the code `cos` of T4–T6 and T4 at offset `flSupOff`. -/
def flCos (cos : List Expr) : List Expr := asmPad flSupOff cos ++ flSup

theorem length_flCos {cos : List Expr} (h : cos.length ≤ flSupOff) :
    (flCos cos).length ≤ asmSlot - rlCosOff := by
  rw [flCos, List.length_append, length_asmPad h, flSup, length_flSupFuns]
  unfold flSupOff asmSlot rlCosOff; omega

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {hsy : SylowAlgo} {hsc : SylowConjugate} {hnc : NormalClosure}
  {ext : List Prim} {gen cos agg : List Expr}

/-- The code `cos` of T4–T6 sits at `rlb rlCosOff`. -/
theorem fl_hasAt_cos (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ flSupOff) {extra : List Prim} :
    (asmProg hst hm hpre hfac extra gen (rlRow flRad (flCos cos)) agg).HasAt (rlb rlCosOff)
      cos :=
  (rl_hasAt_cos hg length_flRad (length_flCos hc)).left.left

/-- The code of T4 sits at `flSupIdx`. -/
theorem fl_hasAt_sup (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ flSupOff) {extra : List Prim} :
    (asmProg hst hm hpre hfac extra gen (rlRow flRad (flCos cos)) agg).HasAt flSupIdx flSup := by
  have h := (rl_hasAt_cos (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (extra := extra)
    (agg := agg) hg length_flRad (length_flCos hc)).right
  rwa [length_asmPad hc] at h

/-- **The layout `SupAt` of T4 in the final program.** -/
theorem fl_supAt (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ flSupOff) :
    SupAt (asmProg hst hm hpre hfac
        (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ (flSupExtra hsy hsc hnc ++ ext)))
        gen (rlRow flRad (flCos cos)) agg)
      flSupIdx (flSupIdx + 6) (flSupIdx + 1) (flSupIdx + 12) 10 (flSupIdx + 2) (flSupIdx + 9)
      (flSupIdx + 4) (flSupIdx + 19) (flSupIdx + 3) (flSupIdx + 22) 11 13 5 1 (flSupIdx + 27)
      (flSupIdx + 39) (flSupIdx + 5) (flSupIdx + 42) 12 hni hsy hnc hO hm hsc :=
  flSupAt_of (fl_hasAt_sup hg hc) rfl rfl rfl rfl rfl rfl

/-- **T4 in the final program**: `TermSupSpec` at `flSupIdx` (`sup_termSupSpec`). -/
theorem fl_termSupSpec (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ flSupOff) :
    Iface.TermSupSpec (asmProg hst hm hpre hfac
        (gsExtra hmb hO hC ++ (flRadExtra hcs hder hqc hni ++ (flSupExtra hsy hsc hnc ++ ext)))
        gen (rlRow flRad (flCos cos)) agg)
      (supK (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc))
      (supD (normalizedIntersectionPrim hni) (sylowPrim hsy) (normalClosurePrim hnc)
        (groupOrderPrim hO) (membershipPrim hm) (sylowConjugatePrim hsc)) flSupIdx :=
  sup_termSupSpec (fl_supAt hg hc)

end Asm

end GI.Impl
