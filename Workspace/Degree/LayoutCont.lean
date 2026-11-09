module

public import Workspace.Degree.Layout

@[expose] public section

/-!
# The placements of `contD`, the reset and the root in `degProg`

`dp_contCode`, `dp_resetCode` and `dp_rootCode` give the codes `ContCode`, `ResetCode` and
`RootCode` of `degProg`. The new functions sit at their indices in `degFuns` (`dg_one`, `dg_blk`).
The blocks of the general algorithm sit in the core of `asmProg` (`asm_block`, `asm_prepAt`,
`asm_liftAt`).
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor)

set_option maxRecDepth 100000

variable {h : JohnsonRecognition} {E D : ℕ}

/-- The context of the recursion in `degProg`, for the interface `I` and the root bound `Nm`. -/
noncomputable abbrev dpCtx (h : JohnsonRecognition) (E D : ℕ) (I : Iface) (Nm : ℕ) : Ctx :=
  DCtx (degProg h E D) I (dgb 0) (dgb 3) (dgb 20) D Nm

/-- **The code of `contD`** in `degProg`. -/
noncomputable def dp_contCode (I : Iface) (Nm : ℕ) : ContCode (dpCtx h E D I Nm) degF where
  hF := rfl
  bs := 99
  brho := dgb 100
  g := dgb 15
  blog := dgb 160
  bl := 143
  bm := 342
  fs := 0
  forb := dgb 1
  frs := dgb 2
  hcont := dg_one 0 rfl
  hbs := asm_block 99 rfl
  hbr := dg_blk 100 rfl
  hg := dg_one 15 rfl
  hl := dg_blk 160 rfl
  hlo := asm_block 143 rfl
  hmax := asm_block 342 rfl
  obl := 143
  obs := 320
  obg := 338
  obc := 273
  horb := dg_one 1 rfl
  holo := asm_block 143 rfl
  hosp := asm_block 320 rfl
  hoga := asm_block 338 rfl
  hoco := asm_block 273 rfl

/-- **The code of the reset** in `degProg`. -/
noncomputable def dp_resetCode (I : Iface) (Nm : ℕ) :
    ResetCode (dpCtx h E D I Nm) (dgb 2) GI.Proved.pointwiseStab GI.Proved.preimage
      GI.Proved.normalizedFactor where
  prep := 9
  mh := dgb 110
  mi := dgb 16
  red := 104
  dom := 112
  col := 10
  hier := 11
  ap := 137
  rep := 140
  lo := 143
  cnt := 205
  ob := 210
  jst := 0
  lift := 289
  jpre := 2
  jfac := 3
  hb := dg_one 2 rfl
  hp := asm_prepAt
  hjs := rfl
  hm := dg_blk 110 rfl
  hi := dg_one 16 rfl
  hl := asm_liftAt
  hjp := rfl
  hjf := rfl

/-- **The code of the root** in `degProg`. -/
noncomputable def dp_rootCode :
    RootCode (degProg h E D) D GI.Proved.pointwiseStab GI.Proved.preimage
      GI.Proved.normalizedFactor where
  f := dgb 40
  fs := 0
  rf := dgb 41
  contD := dgb 0
  dE := .nat D
  prep := 9
  red := 104
  dom := 112
  col := 10
  hier := 11
  ap := 137
  rep := 140
  lo := 143
  cnt := 205
  ob := 210
  jst := 0
  lift := 289
  jpre := 2
  jfac := 3
  htop := dg_one 40 rfl
  hdE := fun _ => Det.nat D
  hrf := dg_one 41 rfl
  hp := asm_prepAt
  hjs := rfl
  hl := asm_liftAt
  hjp := rfl
  hjf := rfl

end GI.Degree
