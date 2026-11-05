module

public import Workspace.Impl.RowSpecProg
public import Workspace.Impl.TermLift
public import Workspace.Impl.TermSplit
public import Workspace.Impl.TermRepsMain
public import Workspace.Impl.LayoutAsm

@[expose] public section

/-!
# The row step in the concrete program

`rlRow rad cos` is the function list of the row step, placed at `asmRowBase` in `asmProg`
(`rlb i = asmRowBase + i`). It holds the row step (`rsBodyE`) with its modules, the terminal
function (`tmTermBody`) and the chain below it: the assembly T7 (`tmLiftBody`), the split over
the radical cosets (`tmSplitBody`) and the coset representatives T3 (`tmRpEntryF`).

Two pieces of the terminal are hypotheses here: the radical preimage T2 (`TermRadSpec`) and one
radical coset T4–T6 (`TermCosetSpec`). Their code is a parameter: `rad` sits at `rlb rlRadOff`,
`cos` at `rlb rlCosOff`.

Where the functions sit (offsets from `asmRowBase`):

* single functions `0`–`18`: `0` the row step, `1` the terminal, `2` its context, `3` the
  script driver, `4`–`7` one script step, `8` T7, `9` the split, `10` one piece of the split,
  `11` `CombineExact`, `12`–`17` T3, `18` the combination step of `CombineExact`;
* blocks: `20` map of the pieces, `23` fold of `CombineExact`, `26` fold of a T3 round, `29` the
  test `any` of T3, `32` `mkGroup`, `39` inverse, `51` the row labels, `55` the natural-map test,
  `127` the coordinates (A.17), `245` A.18, `380` the column branch;
* `rad` from `1000`, `cos` from `100000`.

Helpers shared with the core of `asmProg`: preparation `9` and lift `289` of a fresh phase,
reduce `104`, domain restriction `112`, append `137`, replicate `140`, compose `273`, coset
normal form `280`, range `286`, gather `338`. Primitives: `PointwiseStab` `0`, `Membership` `1`,
`Preimage` `2`, `NormalizedFactor` `3`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership)

set_option maxRecDepth 100000

/-- The index of entry `i` of the row step. -/
def rlb (i : ℕ) : ℕ := asmRowBase + i

/-- The offset of the radical preimage code (T2). -/
def rlRadOff : ℕ := 1000

/-- The offset of the radical coset code (T4–T6). -/
def rlCosOff : ℕ := 100000

/-- **The fixed functions of the row step.** -/
def rlFixed : List Expr :=
  [rsBodyE (rlb 55) (rlb 51) 286 (rlb 127) (rlb 245) (rlb 380) (rlb 1),
    tmTermBody (rlb 2) (rlb 3) (rlb 8),
    tmPrepBody 104 140,
    runBody asmF (rlb 3) (rlb 4),
    tmStepBody (rlb 5),
    tmAskBody (rlb 6) (rlb 7),
    tmRowBody 338,
    tmValBody 137 (112 + 9),
    tmLiftBody 9 (rlb 9) 289,
    tmSplitBody (rlb 12) 286 (rlb 20) (rlb 11),
    tmPieceF (rlb rlCosOff),
    ceF 137 (rlb 23) 280,
    tmRpEntryF (rlb 13),
    tmRpInnerF (rlb 32) (rlb rlRadOff) 286 (rlb 14),
    tmRpWhileF (rlb 14) (rlb 15),
    tmRpStepF (rlb 26),
    tmRpTestF (rlb 29) 273,
    tmRpPredF 1 273 (rlb 39),
    combStep 273 (rlb 39) 137,
    .nil] ++
  mapFuns (rlb 20) (rlb 10) ++ foldlFuns (rlb 23) (rlb 18) ++ foldlFuns (rlb 26) (rlb 16) ++
  anyFuns (rlb 29) (rlb 17) ++ mkGroupFuns (rlb 32) ++ invFuns (rlb 39) ++ rowPartFuns (rlb 51) ++
  natFuns (rlb 55) 2 ++ coordFuns (rlb 127) 0 3 ++ a18Funs (rlb 245) 0 ++
  colBrFuns (rlb 380) asmF.cont

theorem length_rlFixed : rlFixed.length = 491 := rfl

/-- **The functions of the row step**, with the code `rad` of T2 and `cos` of T4–T6. -/
def rlRow (rad cos : List Expr) : List Expr :=
  asmPad rlRadOff rlFixed ++ asmPad (rlCosOff - rlRadOff) rad ++ cos

theorem length_rlRow {rad cos : List Expr} (hr : rad.length ≤ rlCosOff - rlRadOff) :
    (rlRow rad cos).length = rlCosOff + cos.length := by
  rw [rlRow, List.length_append, List.length_append, length_asmPad hr,
    length_asmPad (by rw [length_rlFixed]; unfold rlRadOff; omega)]
  unfold rlCosOff rlRadOff; omega

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {extra : List Prim} {gen rad cos agg : List Expr}

/-- The row list sits at `asmRowBase`. -/
theorem rl_hasAt (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt asmRowBase (rlRow rad cos) :=
  asmProg_hasAt_row hg (by rw [length_rlRow hr]; unfold asmSlot rlCosOff at *; omega)

theorem rl_hasAt_fixed (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt asmRowBase rlFixed :=
  (rl_hasAt hg hr hc).left.left.left

/-- **The code of T2 sits at `rlb rlRadOff`.** -/
theorem rl_hasAt_rad (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt (rlb rlRadOff) rad := by
  have h := (rl_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (extra := extra)
    (agg := agg) hg hr hc).left.right
  rw [length_asmPad (by rw [length_rlFixed]; unfold rlRadOff; omega)] at h
  exact h.left

/-- **The code of T4–T6 sits at `rlb rlCosOff`.** -/
theorem rl_hasAt_cos (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
    (hc : cos.length ≤ asmSlot - rlCosOff) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt (rlb rlCosOff) cos := by
  have h := (rl_hasAt (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac) (extra := extra)
    (agg := agg) hg hr hc).right
  rw [List.length_append, length_asmPad hr,
    length_asmPad (by rw [length_rlFixed]; unfold rlRadOff; omega)] at h
  have e : asmRowBase + (rlRadOff + (rlCosOff - rlRadOff)) = rlb rlCosOff := by
    unfold rlb rlRadOff rlCosOff; omega
  rwa [e] at h

theorem rl_blk (hF : (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt asmRowBase
    rlFixed) {gs : List Expr} (i : ℕ) (hgs : (rlFixed.drop i).take gs.length = gs) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt (rlb i) gs :=
  hF.block i hgs

theorem rl_one (hF : (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).HasAt asmRowBase
    rlFixed) {e : Expr} (i : ℕ) (hgs : (rlFixed.drop i).take 1 = [e]) :
    (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg).funs[rlb i]? = some e :=
  (rl_blk (gs := [e]) hF i hgs).single

variable (hg : gen.length ≤ asmSlot) (hr : rad.length ≤ rlCosOff - rlRadOff)
  (hc : cos.length ≤ asmSlot - rlCosOff)
include hg hr hc

/-- **The layout of the row step** (`RsAt`). -/
theorem rl_rsAt :
    RsAt (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) asmF hst hfac (rlb 0)
      (rlb 55) 2 (rlb 51) 286 (rlb 127) 0 3 (rlb 245) (rlb 380) (rlb 1) := by
  have hF := rl_hasAt_fixed (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (extra := extra) (agg := agg) hg hr hc
  exact
  { main := rl_one hF 0 rfl
    nat := natAt_of_hasAt (rl_blk hF 55 rfl)
    part := rl_blk hF 51 rfl
    rng := asm_block 286 rfl
    coord := rl_blk hF 127 rfl
    pst := asmProg_prim_pst
    fac := asmProg_prim_fac
    a18 := rl_blk hF 245 rfl
    col := colBrAt_of_hasAt (rl_blk hF 380 rfl) }

/-- **The layout of the terminal function** (`TmFuns`). -/
theorem rl_tmFuns :
    TmFuns (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) asmF hst (rlb 1) (rlb 2) 104 0
      140 (rlb 3) (rlb 4) (rlb 5) (rlb 6) (rlb 7) 338 112 137 (rlb 8) := by
  have hF := rl_hasAt_fixed (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (extra := extra) (agg := agg) hg hr hc
  exact
  { main := rl_one hF 1 rfl
    prep := rl_one hF 2 rfl
    red := asm_block 104 rfl
    prim := asmProg_prim_pst
    repl := asm_block 140 rfl
    drv := rl_one hF 3 rfl
    step :=
      { step := rl_one hF 4 rfl
        ask := rl_one hF 5 rfl
        row := rl_one hF 6 rfl
        gather := asm_block 338 rfl
        val := rl_one hF 7 rfl
        dom := domAt_of_hasAt (asm_block 112 rfl)
        append := asm_block 137 rfl } }

/-- **The layout of T7** (`TmLiftAt`): the preparation and the lift of the core. -/
theorem rl_liftAt :
    TmLiftAt (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) (rlb 8) 9 104 112 10 11 137
      140 143 205 210 0 (rlb 9) 289 2 3 := by
  have hF := rl_hasAt_fixed (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (extra := extra) (agg := agg) hg hr hc
  exact
  { entry := rl_one hF 8 rfl
    prepAt := asm_prepAt
    liftAt := asm_liftAt }

/-- **The layout of the split** (`TmSplitAt`). -/
theorem rl_splitAt :
    TmSplitAt (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) (rlb 9) (rlb 12)
      (rlb rlCosOff) 286 (rlb 20) (rlb 10) (rlb 11) 137 (rlb 23) (rlb 18) 273 (rlb 39) 137 280 1 := by
  have hF := rl_hasAt_fixed (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (extra := extra) (agg := agg) hg hr hc
  exact
  { entry := rl_one hF 9 rfl
    piece := rl_one hF 10 rfl
    range := asm_block 286 rfl
    map := rl_blk hF 20 rfl
    ce := rl_one hF 11 rfl
    ap := asm_block 137 rfl
    fold := rl_blk hF 23 rfl
    step := rl_one hF 18 rfl
    comp := asm_block 273 rfl
    inv := rl_blk hF 39 rfl
    app := asm_block 137 rfl
    nf := asm_block 280 rfl }

/-- **The layout of T3** (`TmRpAt`). -/
theorem rl_repsAt :
    TmRpAt (asmProg hst hm hpre hfac extra gen (rlRow rad cos) agg) hm (rlb 12) (rlb 13) (rlb 32)
      (rlb rlRadOff) 286 (rlb 14) (rlb 15) (rlb 26) (rlb 16) (rlb 29) (rlb 17) 1 273 (rlb 39) := by
  have hF := rl_hasAt_fixed (hst := hst) (hm := hm) (hpre := hpre) (hfac := hfac)
    (extra := extra) (agg := agg) hg hr hc
  exact
  { entry := rl_one hF 12 rfl
    inner := rl_one hF 13 rfl
    mkg := rl_blk hF 32 rfl
    rg := asm_block 286 rfl
    wh := rl_one hF 14 rfl
    round :=
      { step := rl_one hF 15 rfl
        fold := rl_blk hF 26 rfl
        test := rl_one hF 16 rfl
        any := rl_blk hF 29 rfl
        pred := rl_one hF 17 rfl
        mem := asmProg_prim_mem
        comp := asm_block 273 rfl
        inv := rl_blk hF 39 rfl } }

end Asm

end GI.Impl
