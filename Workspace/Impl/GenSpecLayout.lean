import Workspace.Impl.GenSpecNorm
import Workspace.Impl.GenNormOps
import Workspace.Impl.LayoutAsm

/-!
# The general dispatcher in the concrete program

`gsGen` is the function list of the general dispatcher, placed at `asmGenBase` in `asmProg`
(`gsb i = asmGenBase + i`). The extra primitives are `gsExtra = [MinimalBlocks, GroupOrder,
CameronRecognition]`, at `4, 5, 6`; the step also uses `PointwiseStab`, `Membership` and
`Preimage` at `0, 1, 2`.

Single functions (`0`–`43`): `0` the step (`gsGenE`), `1`–`2` the exposure, `3` the case
decision, `4` the branch, `5`–`8` the enumeration, `9`–`25` the product step, `26`–`43` the
normalization (adapter, step, preparation, parent pairs, preparation helpers, tail and child).
Blocks from `50` on (see `gsGen`).

`gs_asm_general`: `Iface.GeneralSpec` for `asmRest … gsWg Wr Wa` and `asmProg … gsExtra gsGen
row agg`, with the work `gsWg nd = gsOwn k (stateW k S)` at every node (`k = |Ω|`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition)

set_option maxRecDepth 100000

/-- The index of entry `i` of the general dispatcher. -/
def gsb (i : ℕ) : ℕ := asmGenBase + i

/-- The body of the normalization preparation (`normPrepF`) with its indices as arguments. -/
def gsNormPrepE (cls range pmap alt pre raw cosets selection count blockmap labels orbit : ℕ) :
    Expr :=
  .letE (.call cls (mk2 (normInput 1) (normState 2)))
  (.letE (.call range (.length (normField 1 1)))
  (.letE (.call range (normInput 3))
  (.letE (.call pmap (mk2 normPairContext normParentGenerators))
  (.letE (.call alt (normInput 3))
  (.letE (.call pre (Expr.mkList [mk2 (normState 0) (normInput 3), .var 4, .var 5]))
  (.letE (.call raw (mk2 (normState 0) (.var 6)))
  (.letE (.call pmap (mk2 normPairContext (normField 7 1)))
  (.letE (.call cosets (mk2 (mk2 (normField 7 0) normPositionIds) normParentGenerators))
  (.letE (.call selection (mk2 (normState 2) (normInput 2)))
  (.letE (.call count (mk2 (.nat 0) (normField 1 0)))
  (.letE (.call blockmap (mk2 (Expr.mkList
    [normInput 5, normField 1 0, normState 2, .var 3, normFlip]) normPositionIds))
  (.letE (.call labels (Expr.mkList
    [normInput 3, normInput 4, .var 8, .var 10, .var 11, .var 12]))
  (.letE (.call orbit (mk2 (normField 7 0) (normState 2)))
  (mk2 (Expr.mkList [normInput 0, normField 7 0, normInput 2, .var 13, .var 14])
    (.var 9)))))))))))))))

theorem normPrepF_eq {Pg : Program} {hp : Preimage} {hst : PointwiseStab} {hm : Membership}
    (o : normOps Pg hp hst hm) :
    normPrepF o = gsNormPrepE o.cls o.range o.pairs.map o.alt o.pre o.raw o.cosets o.selection
      o.count o.blockmap o.labels o.orbit := rfl

/-- **The functions of the general dispatcher.** -/
def gsGen : List Expr :=
  [gsGenE (gsb 1) 5 (gsb 3) (gsb 4),
    exposeE (gsb 2) 4 (gsb 103) (gsb 50) (gsb 94) (gsb 107),
    prepE (gsb 74) (gsb 83) (gsb 50) (gsb 86) (gsb 94),
    caseBody (gsb 112) 5 6,
    branchE (gsb 5) (gsb 9) (gsb 26),
    -- the enumeration
    enumF (gsb 119) (gsb 154) (gsb 6),
    tailF (gsb 405) (gsb 206) (gsb 200),
    enumChildF asmF (gsb 103),
    combStep (gsb 181) (gsb 185) (gsb 197),
    -- the product step
    prodE (gsb 10) (gsb 417) (gsb 218) (gsb 119) (gsb 426) (gsb 429) (gsb 21) (gsb 22) (gsb 6),
    ptabsE (gsb 11) (gsb 83) (gsb 411) (gsb 414),
    prowsE (gsb 408) (gsb 209) (gsb 103),
    addOneF,
    pselF (gsb 215) 0,
    pselF (gsb 215) 1,
    tabWrapF (gsb 420),
    sqEntF,
    tabWrapF (gsb 423),
    unsqEntF,
    pairUnsqF (gsb 17),
    oneF,
    pkerE (gsb 50) (gsb 154) (gsb 432) (gsb 221),
    phierE (gsb 226) (gsb 229) (gsb 235),
    cvF (gsb 435),
    cvLabF (gsb 232),
    cvTestF,
    -- the normalization
    gsNormE (gsb 27),
    normStepF (gsb 28) (gsb 42),
    gsNormPrepE (gsb 50) (gsb 83) (gsb 438) (gsb 34) (gsb 260) (gsb 35) (gsb 36) (gsb 74)
      (gsb 333) (gsb 444) (gsb 41) (gsb 40),
    normParentF (gsb 30) (gsb 441),
    actF (gsb 103),
    normPointF (gsb 242),
    normCandidateF (gsb 245),
    normIncTestF (gsb 238),
    normAltF (gsb 209) (gsb 248),
    normRawReduceF (gsb 310) 0,
    normCosetsF (gsb 330),
    normOutsideF 1,
    normBlockCellF (gsb 447),
    normMemFlipF (gsb 238),
    normOrbitF (gsb 338) (gsb 400),
    normLabelBuildF,
    tailF (gsb 450) (gsb 206) (gsb 200),
    normChildF asmF (gsb 103),
    .nil, .nil, .nil, .nil, .nil, .nil] ++
  clsFuns (gsb 50) ++ hsplitFuns (gsb 74) (gsb 50) ++ rangeFuns (gsb 83) ++ baseFuns (gsb 86) ++
  actFuns (gsb 94) ++ gatherFuns (gsb 103) ++ hierFuns (gsb 107) ++ smallZFuns (gsb 112) 24953 ++
  cosetsFuns (gsb 119) ++ kerNFFuns (gsb 154) 2 1 ++ composeFuns (gsb 181) ++ invFuns (gsb 185) ++
  appendFuns (gsb 197) ++ cosetNFFuns (gsb 200) 1 ++ foldlFuns (gsb 206) (gsb 8) ++
  replicateFuns (gsb 209) ++ eqNatsFuns (gsb 212) ++ pbFuns (gsb 215) (gsb 212) ++
  factFuns (gsb 218) ++ reduceFuns (gsb 221) 1 ++ chooseFuns (gsb 226) ++
  cvAllFuns (gsb 229) (gsb 23) ++ findFuns (gsb 232) (gsb 25) ++ spliceFuns (gsb 235) (gsb 197) ++
  normMemFuns (gsb 238) ++ filterFuns (gsb 242) (gsb 32) ++ allFuns (gsb 245) (gsb 33) ++
  cycGensFuns (gsb 248) ++ graphPreFuns (gsb 260) 2 ++ krFuns (gsb 310) 0 ++
  filterFuns (gsb 330) (gsb 37) ++ countFuns (gsb 333) ++ loFuns (gsb 338) ++ maxFuns (gsb 400) ++
  mapFuns (gsb 405) (gsb 7) ++ mapFuns (gsb 408) (gsb 12) ++ mapFuns (gsb 411) (gsb 13) ++
  mapFuns (gsb 414) (gsb 14) ++ mapFuns (gsb 417) (gsb 15) ++ mapFuns (gsb 420) (gsb 16) ++
  mapFuns (gsb 423) (gsb 18) ++ mapFuns (gsb 426) (gsb 19) ++ mapFuns (gsb 429) (gsb 20) ++
  mapFuns (gsb 432) (gsb 17) ++ mapFuns (gsb 435) (gsb 24) ++ mapFuns (gsb 438) (gsb 29) ++
  mapFuns (gsb 441) (gsb 31) ++ mapFuns (gsb 444) (gsb 38) ++ mapFuns (gsb 447) (gsb 39) ++
  mapFuns (gsb 450) (gsb 43)

theorem length_gsGen : gsGen.length = 453 := rfl

/-- The extra primitives: `MinimalBlocks` at `4`, `GroupOrder` at `5`, `CameronRecognition` at
`6`. -/
noncomputable def gsExtra (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition) :
    List Prim :=
  [minimalBlocksPrim hmb, groupOrderPrim hO, cameronRecognitionPrim hC]

/-- **The work of the general dispatcher at a node**: `gsOwn k (stateW k S)` for `k = |Ω|`. -/
noncomputable def gsWg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition) (nd : Node P₀) : ℝ :=
  (gsOwn hmb hO hC hpre hm (gsCn hpre hst hm) (Nat.card nd.Ω) (stateW (Nat.card nd.Ω) nd.S) : ℕ)

section Asm

variable {Pg : Program}

theorem gs_blk (hG : Pg.HasAt asmGenBase gsGen) {gs : List Expr} (i : ℕ)
    (hg : (gsGen.drop i).take gs.length = gs) : Pg.HasAt (gsb i) gs :=
  hG.block i hg

theorem gs_one (hG : Pg.HasAt asmGenBase gsGen) {e : Expr} (i : ℕ)
    (hg : (gsGen.drop i).take 1 = [e]) : Pg.funs[gsb i]? = some e :=
  (gs_blk (gs := [e]) hG i hg).single

end Asm

/-- **The general dispatcher of the concrete program meets its step specification**, for the
work `gsWg`, given the cited `MinimalBlocks`, `GroupOrder` and `CameronRecognition` (and the
primitives of `asmProg`). Any list `ext` of further primitives may follow `gsExtra` (from index
`7` on). -/
theorem gs_asm_general_ext (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (ext : List Prim) (row agg : List Expr) (Wr Wa : Node P₀ → ℝ) :
    (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.GeneralSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row agg) asmF asmGenBase := by
  set R := asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa with hR
  set Pg := asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ ext) gsGen row agg with hPg
  have hG : Pg.HasAt asmGenBase gsGen :=
    asmProg_hasAt_gen (by rw [length_gsGen]; unfold asmSlot; omega)
  have p0 : Pg.prims[0]? = some (pointwiseStabPrim hst) := rfl
  have p1 : Pg.prims[1]? = some (membershipPrim hm) := rfl
  have p2 : Pg.prims[2]? = some (preimagePrim hpre) := rfl
  have p4 : Pg.prims[4]? = some (minimalBlocksPrim hmb) := rfl
  have p5 : Pg.prims[5]? = some (groupOrderPrim hO) := rfl
  have p6 : Pg.prims[6]? = some (cameronRecognitionPrim hC) := rfl
  have hexp : ExposeAt hmb Pg (gsb 1) :=
    exposeAt_of hmb (gs_one hG 1 rfl) (gs_one hG 2 rfl) (gs_blk hG 74 rfl) (gs_blk hG 83 rfl)
      (gs_blk hG 50 rfl) (gs_blk hG 86 rfl) (gs_blk hG 94 rfl) (gs_blk hG 103 rfl)
      (gs_blk hG 107 rfl) p4
  have hcase : CaseAt hO hC Pg (gsb 3) :=
    caseAt_of hO hC (gs_one hG 3 rfl) (gs_blk hG 112 rfl) p5 p6
  have hen : EnumAt R.iface hpre hm Pg asmF (gsb 5) :=
    enumAt_of R.iface hpre hm (gs_one hG 5 rfl) (gs_blk hG 119 rfl) (gs_blk hG 154 rfl) p2
      (gs_one hG 6 rfl) (gs_blk hG 405 rfl) (gs_one hG 7 rfl) (gs_blk hG 103 rfl)
      (gs_blk hG 206 rfl) (gs_one hG 8 rfl) (gs_blk hG 181 rfl) (gs_blk hG 185 rfl)
      (gs_blk hG 197 rfl) (gs_blk hG 200 rfl) p1
  have hpr : ProdAt R.iface hpre hm Pg asmF (gsb 9) :=
    prodAt_of R.iface hpre hm (gs_one hG 9 rfl)
      (gs_one hG 10 rfl) (gs_one hG 11 rfl) (gs_blk hG 408 rfl) (gs_one hG 12 rfl)
      (gs_blk hG 209 rfl) (gs_blk hG 103 rfl) (gs_blk hG 83 rfl) (gs_blk hG 411 rfl)
      (gs_one hG 13 rfl) (gs_blk hG 414 rfl) (gs_one hG 14 rfl) (gs_blk hG 215 rfl)
      (gs_blk hG 212 rfl)
      (gs_blk hG 417 rfl) (gs_one hG 15 rfl) (gs_blk hG 420 rfl) (gs_one hG 16 rfl)
      (gs_one hG 17 rfl) (gs_blk hG 423 rfl) (gs_one hG 18 rfl)
      (gs_blk hG 218 rfl) (gs_blk hG 119 rfl) (gs_blk hG 426 rfl) (gs_one hG 19 rfl)
      (gs_blk hG 429 rfl) (gs_one hG 20 rfl)
      (gs_one hG 21 rfl) (gs_blk hG 50 rfl) (gs_blk hG 154 rfl) p2 p1 (gs_blk hG 432 rfl)
      (gs_blk hG 221 rfl)
      (gs_one hG 22 rfl) (gs_blk hG 226 rfl) (gs_blk hG 229 rfl) (gs_one hG 23 rfl)
      (gs_blk hG 435 rfl) (gs_one hG 24 rfl) (gs_blk hG 232 rfl) (gs_one hG 25 rfl)
      (gs_blk hG 235 rfl) (gs_blk hG 197 rfl)
      (gs_one hG 6 rfl) (gs_blk hG 405 rfl) (gs_one hG 7 rfl) (gs_blk hG 103 rfl)
      (gs_blk hG 206 rfl) (gs_one hG 8 rfl) (gs_blk hG 181 rfl) (gs_blk hG 185 rfl)
      (gs_blk hG 200 rfl)
  let o : normOps Pg hpre hst hm :=
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
      hpre := gs_blk hG 260 rfl, hjpre := p2, hraw := gs_one hG 35 rfl,
      hkr := gs_blk hG 310 rfl, hjst := p0, hcosets := gs_one hG 36 rfl,
      houtsideFilter := gs_blk hG 330 rfl, houtside := gs_one hG 37 rfl, hjm := p1,
      hselection := gs_blk hG 74 rfl, hcount := gs_blk hG 333 rfl,
      hblockmap := gs_blk hG 444 rfl, hcell := gs_one hG 38 rfl, hbits := gs_blk hG 447 rfl,
      hbit := gs_one hG 39 rfl, hmem := gs_blk hG 238 rfl, horbit := gs_one hG 40 rfl,
      hlo := gs_blk hG 338 rfl, hmax := gs_blk hG 400 rfl, hlabels := gs_one hG 41 rfl }
  let t : normTailAt Pg asmF hm :=
    { tail := gsb 42, map := gsb 450, child := gsb 43, gather := gsb 103, combine := gsb 206,
      step := gsb 8, compose := gsb 181, inverse := gsb 185, append := gsb 197, nf := gsb 200,
      membership := 1,
      htail := gs_one hG 42 rfl, hmap := gs_blk hG 450 rfl, hchild := gs_one hG 43 rfl,
      hgather := gs_blk hG 103 rfl, hcombine := gs_blk hG 206 rfl, hstep := gs_one hG 8 rfl,
      hcompose := gs_blk hG 181 rfl, hinverse := gs_blk hG 185 rfl,
      happend := gs_blk hG 197 rfl, hnf := gs_blk hG 200 rfl, hmembership := p1 }
  have hprep : Pg.funs[gsb 28]? = some (normPrepF o) := by
    rw [normPrepF_eq]; exact gs_one hG 28 rfl
  have hno : NormSpec R.iface Pg asmF (gsb 26) (gsCn hpre hst hm) :=
    gs_normSpec R hpre hst hm o t (fn := gsb 27) (gs_one hG 27 rfl) hprep (gs_one hG 26 rfl)
  have hCn : ∀ {k W W' : ℕ}, W ≤ W' → gsCn hpre hst hm k W ≤ gsCn hpre hst hm k W' :=
    fun h => gsCn_mono hpre hst hm h
  have hbr : BranchAt R.iface hpre hm (gsCn hpre hst hm) Pg asmF (gsb 4) :=
    branchAt_of R.iface hpre hm (gs_one hG 4 rfl) hen hpr hno hCn
  have hW : ∀ nd : Node P₀, nd.run.kind = .dispatch ∨ nd.run.kind = .normalize →
      (gsOwn hmb hO hC hpre hm (gsCn hpre hst hm) (Nat.card nd.Ω)
        (stateW (Nat.card nd.Ω) nd.S) : ℝ) ≤ R.iface.W nd := by
    rintro nd (hk | hk) <;> simp only [Rest.iface, Rest.W, hk, hR, asmRest, gsWg, le_refl]
  have h0 := gs_one (e := gsGenE (gsb 1) 5 (gsb 3) (gsb 4)) hG 0 rfl
  rw [show gsb 0 = asmGenBase from Nat.add_zero _] at h0
  intro Ω C S k e c hc v hv hg hP hIH
  exact gs_general_spec R.iface hmb hO hC hpre hm (Cn := gsCn hpre hst hm) hCn h0 hexp p5 hcase
    hbr hW S k e c hc v hv hg hP hIH

/-- `gs_asm_general_ext` with the table `[pst, mem, pre, fac] ++ gsExtra`. -/
theorem gs_asm_general (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (row agg : List Expr) (Wr Wa : Node P₀ → ℝ) :
    (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.GeneralSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC) gsGen row agg) asmF asmGenBase := by
  have h : (asmRest hst hm hpre hfac (gsWg hst hm hpre hmb hO hC) Wr Wa).iface.GeneralSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ []) gsGen row agg) asmF asmGenBase :=
    gs_asm_general_ext hst hm hpre hfac hmb hO hC [] row agg Wr Wa
  rwa [List.append_nil] at h

end GI.Impl
