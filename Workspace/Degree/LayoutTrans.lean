module

public import Workspace.Degree.LayoutCont

@[expose] public section

/-!
# The placements of `transD` in `degProg`

`dp_transCode` gives `TransCode` for `degProg`. The exposure of a quotient, the blocks of the
enumeration and of the product, and the preparation of the normalization are those of the general
dispatcher of the general algorithm in `gsGen` (`gs_blk`, `gs_one`), at the indices that
`gs_asm_general_ext` uses. The three branches meet their named statements by `enum_spec`,
`prod_specD` and `normStep_specD`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val)

set_option maxRecDepth 100000

variable {h : JohnsonRecognition} {E D : ℕ}

/-- The operations of the normalization step of the general algorithm, in `degProg`. -/
noncomputable def dp_normOps :
    normOps (degProg h E D) GI.Proved.preimage GI.Proved.pointwiseStab GI.Proved.membership :=
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  { pairs :=
      { map := gsb 438, parent := gsb 29, act := gsb 30, gather := gsb 103,
        recover := gsb 441, point := gsb 31, filter := gsb 242, cand := gsb 32,
        all := gsb 245, test := gsb 33, mem := gsb 238,
        hmap := gs_blk hG 438 rfl, hparent := gs_one hG 29 rfl, hact := gs_one hG 30 rfl,
        hgather := gs_blk hG 103 rfl, hrecover := gs_blk hG 441 rfl,
        hpoint := gs_one hG 31 rfl, hfilter := gs_blk hG 242 rfl, hcand := gs_one hG 32 rfl,
        hall := gs_blk hG 245 rfl, htest := gs_one hG 33 rfl, hmem := gs_blk hG 238 rfl }
    cls := gsb 50, range := gsb 83, alt := gsb 34, replicate := gsb 209, cycles := gsb 248,
    pre := gsb 260, jpre := 2, raw := gsb 35, kr := gsb 310, jst := 0, cosets := gsb 36,
    outsideFilter := gsb 330, outside := gsb 37, jm := 1, selection := gsb 74,
    count := gsb 333, blockmap := gsb 444, cell := gsb 38, bits := gsb 447, bit := gsb 39,
    mem := gsb 238, orbit := gsb 40, lo := gsb 338, max := gsb 400, labels := gsb 41,
    hcls := gs_blk hG 50 rfl, hrange := gs_blk hG 83 rfl, halt := gs_one hG 34 rfl,
    hreplicate := gs_blk hG 209 rfl, hcycles := gs_blk hG 248 rfl,
    hpre := gs_blk hG 260 rfl, hjpre := rfl, hraw := gs_one hG 35 rfl,
    hkr := gs_blk hG 310 rfl, hjst := rfl, hcosets := gs_one hG 36 rfl,
    houtsideFilter := gs_blk hG 330 rfl, houtside := gs_one hG 37 rfl, hjm := rfl,
    hselection := gs_blk hG 74 rfl, hcount := gs_blk hG 333 rfl,
    hblockmap := gs_blk hG 444 rfl, hcell := gs_one hG 38 rfl, hbits := gs_blk hG 447 rfl,
    hbit := gs_one hG 39 rfl, hmem := gs_blk hG 238 rfl, horbit := gs_one hG 40 rfl,
    hlo := gs_blk hG 338 rfl, hmax := gs_blk hG 400 rfl, hlabels := gs_one hG 41 rfl }

/-- The tail of the normalization step, with the new child function at `dgb 14`. -/
noncomputable def dp_normTail : normTailAt (degProg h E D) degF GI.Proved.membership :=
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  { tail := dgb 12, map := dgb 150, child := dgb 14, gather := gsb 103, combine := gsb 206,
    step := gsb 8, compose := gsb 181, inverse := gsb 185, append := gsb 197, nf := gsb 200,
    membership := 1,
    htail := dg_one 12 rfl, hmap := dg_blk 150 rfl, hchild := dg_one 14 rfl,
    hgather := gs_blk hG 103 rfl, hcombine := gs_blk hG 206 rfl, hstep := gs_one hG 8 rfl,
    hcompose := gs_blk hG 181 rfl, hinverse := gs_blk hG 185 rfl,
    happend := gs_blk hG 197 rfl, hnf := gs_blk hG 200 rfl, hmembership := rfl }

theorem dp_enumAt :
    EnumAt (degProg h E D) degF GI.Proved.preimage GI.Proved.membership (dgb 6) := by
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  intro Ω C k Bc e c gv dv xv yv hv rv fv hh N S hcan Q hkeep lv hv' hR hH B hB hcall
  exact enum_spec Bc GI.Proved.preimage GI.Proved.membership (dg_one 6 rfl) (gs_blk hG 119 rfl)
    (gs_blk hG 154 rfl) rfl (dg_one 9 rfl) (dg_blk 140 rfl) (dg_one 13 rfl) (gs_blk hG 103 rfl)
    (gs_blk hG 206 rfl) (gs_one hG 8 rfl) (gs_blk hG 181 rfl) (gs_blk hG 185 rfl)
    (gs_blk hG 197 rfl) (gs_blk hG 200 rfl) rfl hcan Q hkeep hR hH hB hcall

theorem dp_prodAt :
    ProdAt (degProg h E D) degF GI.Proved.groupOrder GI.Proved.preimage GI.Proved.membership
      (dgb 7) := by
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  intro Ω C Bc k e c gv dv xv yv hv rv fv hh N S hcan Q m l r Em hS hr hkeep gv' rep hv' hH hcall
  exact prod_specD Bc GI.Proved.groupOrder GI.Proved.preimage GI.Proved.membership
    (dg_one 7 rfl) rfl
    (gs_one hG 10 rfl) (gs_one hG 11 rfl) (gs_blk hG 408 rfl) (gs_one hG 12 rfl)
    (gs_blk hG 209 rfl) (gs_blk hG 103 rfl) (gs_blk hG 83 rfl) (gs_blk hG 411 rfl)
    (gs_one hG 13 rfl) (gs_blk hG 414 rfl) (gs_one hG 14 rfl) (gs_blk hG 215 rfl)
    (gs_blk hG 212 rfl)
    (gs_blk hG 417 rfl) (gs_one hG 15 rfl) (gs_blk hG 420 rfl) (gs_one hG 16 rfl)
    (gs_one hG 17 rfl) (gs_blk hG 423 rfl) (gs_one hG 18 rfl)
    (gs_blk hG 119 rfl) (gs_blk hG 426 rfl) (gs_one hG 19 rfl)
    (gs_blk hG 429 rfl) (gs_one hG 20 rfl)
    (gs_one hG 21 rfl) (gs_blk hG 50 rfl) (gs_blk hG 154 rfl) rfl rfl (gs_blk hG 432 rfl)
    (gs_blk hG 221 rfl)
    (gs_one hG 22 rfl) (gs_blk hG 226 rfl) (gs_blk hG 229 rfl) (gs_one hG 23 rfl)
    (gs_blk hG 435 rfl) (gs_one hG 24 rfl) (gs_blk hG 232 rfl) (gs_one hG 25 rfl)
    (gs_blk hG 235 rfl) (gs_blk hG 197 rfl)
    (dg_one 9 rfl) (dg_blk 140 rfl) (dg_one 13 rfl) (gs_blk hG 103 rfl)
    (gs_blk hG 206 rfl) (gs_one hG 8 rfl) (gs_blk hG 181 rfl) (gs_blk hG 185 rfl)
    (gs_blk hG 200 rfl) hcan Q Em hS hr hkeep hH hcall

theorem dp_normAt :
    NormAt (degProg h E D) degF GI.Proved.preimage GI.Proved.pointwiseStab GI.Proved.membership
      (dgb 11) := by
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  have hprep : (degProg h E D).funs[gsb 28]? = some (normPrepF (dp_normOps (h := h) (E := E) (D := D))) := by
    rw [normPrepF_eq]; exact gs_one hG 28 rfl
  intro Ω C _ n m k sz en cc S Bg gv dv xv yv hv rv fv hh rep hv' hcan hne htr Q e hS hq hkc hkl
    hrep hH hcall
  exact normStep_specD GI.Proved.preimage GI.Proved.pointwiseStab GI.Proved.membership
    (dp_normOps (h := h) (E := E) (D := D)) dp_normTail (dg_one 11 rfl) hprep en cc Bg hcan hne htr Q e hS hq hkc hkl hrep hH
    hcall

/-- **The code of `transD`** in `degProg`. -/
noncomputable def dp_transCode (I : Iface) (Nm : ℕ) :
    TransCode (dpCtx h E D I Nm) degF GI.Proved.minimalBlocks GI.Proved.groupOrder h
      GI.Proved.preimage GI.Proved.pointwiseStab GI.Proved.membership :=
  have hG : (degProg h E D).HasAt asmGenBase gsGen := dp_hasAt_gen
  { hcont := rfl
    hgiant := rfl
    fexp := gsb 1
    jo := 5
    fcase := dgb 4
    tst := dgb 120
    jr := degJr
    fbr := dgb 5
    fen := dgb 6
    fpr := dgb 7
    fno := dgb 8
    fs := 0
    fad := dgb 10
    fn := dgb 11
    E := E
    hf := dg_one 3 rfl
    hexp := exposeAt_of GI.Proved.minimalBlocks (gs_one hG 1 rfl) (gs_one hG 2 rfl)
      (gs_blk hG 74 rfl) (gs_blk hG 83 rfl) (gs_blk hG 50 rfl) (gs_blk hG 86 rfl)
      (gs_blk hG 94 rfl) (gs_blk hG 103 rfl) (gs_blk hG 107 rfl) rfl
    hjo := rfl
    hc := dg_one 4 rfl
    htst := dg_blk 120 rfl
    hjr := dp_prim_recog
    hbr := dg_one 5 rfl
    hgate := dg_one 8 rfl
    had := dg_one 10 rfl
    en := dp_enumAt
    pr := dp_prodAt
    no := dp_normAt }

end GI.Degree
