module

public import Workspace.Impl.AggItemCiSojProg
public import Workspace.Impl.FinLayoutItemsOK

@[expose] public section

/-!
# The room of the first-rectangle item

The first-rectangle item (`sojItem`) sits at `fitC23Idx + 101000`, the end of the
pair room (`fc10PrF`). Its list `fc11Conc b` holds every function that `itcsSojOk` asks for, at
fixed offsets from the base `b`:

* 0, 1, 2: the init `.nil`, the source dispatch `itcsStartF` and the step `itcsQueueF`;
* then the source dispatch, the rectangle controller, the query constructor, the
  colored-partition item, the Case 1 item, the component table and the answer finalizer,
  each with the library blocks it calls (copies inside the room).

Two callees lie outside the room: the certificate search at `fitRcIdx` and the rectangle
representation program at `fitRpIdx`. The normalized-factor primitive is prim `3`.
The Case 1 indices `fc11C1 b` are shared by the colored-partition item and the component table.

`fc11_sojOk` reads the table: a program holding `fc11Conc b` at `b` meets `itcsSojOk`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (NormalizedFactor)

/-- The functions of the first-rectangle item at base `b`. -/
noncomputable def fc11Conc (b : ℕ) : List Expr :=
  [.nil] ++ (
  [itcsStartF (b + 3) (b + 11) (b + 70) (b + 24) (b + 13) (b + 17) (b + 22) fitRcIdx (b + 23)] ++ (
  [itcsQueueF (b + 237)] ++ (
  [itcsFrontF (b + 70) (b + 4) (b + 7)] ++ (
  filterFuns (b + 4) (b + 28) ++ (
  findFuns (b + 7) (b + 10) ++ (
  [itcsTestF (b + 11) (b + 12)] ++ (
  [itcqPcF] ++ (
  [itcsSizeF (b + 198) (b + 125)] ++ (
  allFuns (b + 13) (b + 16) ++ (
  [itcsBalTestF (b + 125)] ++ (
  [itcsImpPartF (b + 70) (b + 198) (b + 18) (b + 120)] ++ (
  allFuns (b + 18) (b + 21) ++ (
  [itcsMinF (b + 28) (b + 125)] ++ (
  [itcsBalPartF (b + 70) (b + 24) (b + 105)] ++ (
  [itcsRectPrepF (b + 70) (b + 24) (b + 29) (b + 33) (b + 34) (b + 35) (b + 41) (b + 44) fitRpIdx (b + 49)] ++ (
  mapFuns (b + 24) (b + 27) ++ (
  [itcsBalB (b + 28)] ++ (
  [itcqFbT] ++ (
  mapFuns (b + 29) (b + 32) ++ (
  [itcsSideF] ++ (
  [itcsGuardF (b + 126)] ++ (
  [itcsAlignF (b + 105)] ++ (
  [itcsFixProgF (b + 70) (b + 36) (b + 40)] ++ (
  mapFuns (b + 36) (b + 39) ++ (
  [itcsFixMarkF] ++ (
  [itcsFixGenF (b + 105)] ++ (
  mapFuns (b + 41) (b + 47) ++ (
  mapFuns (b + 44) (b + 48) ++ (
  [itcsMarkF 2] ++ (
  [itcsMarkF 1] ++ (
  [itcsAskF (b + 50) (b + 51)] ++ (
  [itcsPhysicalDataF (b + 52) (b + 64) (b + 70) (b + 91)] ++ (
  [itcsColorsStateF (b + 95) (b + 70) (b + 99) (b + 104)] ++ (
  [itcsPhysF (b + 53) (b + 57)] ++ (
  mapFuns (b + 53) (b + 56) ++ (
  [krFstF] ++ (
  mkGroupFuns (b + 57) ++ (
  [itcsSwapLcF (b + 65) (b + 69)] ++ (
  swapMapFuns (b + 65) ++ (
  [itHvLcF (b + 70) (b + 73) (b + 87)] ++ (
  rangeFuns (b + 70) ++ (
  [grpF (b + 74) (b + 57)] ++ (
  pEncMapFuns (b + 74) ++ (
  fstMapFuns (b + 87) ++ (
  mapFuns (b + 91) (b + 94) ++ (
  [itcsDomB] ++ (
  composeFuns (b + 95) ++ (
  mapFuns (b + 99) (b + 102) ++ (
  [itcsPullB (b + 103)] ++ (
  [itcsPullF] ++ (
  [itcsStateF] ++ (
  [itciF (b + 70) (b + 106) (b + 107) (b + 111) (b + 185) (b + 95)] ++ (
  [itciAF (b + 70) (b + 131) (b + 139) (b + 95)] ++ (
  allFuns (b + 107) (b + 110) ++ (
  [itciChkT] ++ (
  [itciGF (b + 112) (b + 156) (b + 165) (b + 160) (b + 180)] ++ (
  mapFuns (b + 112) (b + 115) ++ (
  [itciCB (b + 116)] ++ (
  findFuns (b + 116) (b + 119) ++ (
  [itciEqT] ++ (
  [itC1F (b + 121) (b + 151) (b + 156) (b + 160) (b + 164) (b + 180) (b + 95) (b + 185)] ++ (
  [itDatF (b + 70) (b + 122) (b + 131) (b + 139)] ++ (
  mapFuns (b + 122) (b + 125) ++ (
  [itSzB (b + 126)] ++ (
  countFuns (b + 126) ++ (
  mapFuns (b + 131) (b + 134) ++ (
  [itPosB (b + 135)] ++ (
  filterFuns (b + 135) (b + 138) ++ (
  [itKeyB] ++ (
  invFuns (b + 139) ++ (
  [itChkF (b + 70) (b + 152)] ++ (
  allFuns (b + 152) (b + 155) ++ (
  [itCntT (b + 126)] ++ (
  findFuns (b + 156) (b + 159) ++ (
  [itFixT] ++ (
  mapFuns (b + 160) (b + 163) ++ (
  [itSwB] ++ (
  [itGensF (b + 165) (b + 70) (b + 169) (b + 177)] ++ (
  mapFuns (b + 165) (b + 168) ++ (
  [itTrB (b + 160)] ++ (
  mapFuns (b + 169) (b + 172) ++ (
  [itGenB (b + 173)] ++ (
  mapFuns (b + 173) (b + 176) ++ (
  [itBsB] ++ (
  appendFuns (b + 177) ++ (
  [itSchF (b + 70) (b + 181)] ++ (
  mapFuns (b + 181) (b + 184) ++ (
  [itSchB (b + 185) (b + 95)] ++ (
  [itParF (b + 70) (b + 186) (b + 194)] ++ (
  mapFuns (b + 186) (b + 189) ++ (
  [itInvB (b + 190)] ++ (
  filterFuns (b + 190) (b + 193) ++ (
  [itInvT] ++ (
  foldlFuns (b + 194) (b + 197) ++ (
  [itParS] ++ (
  [itcsCompF (b + 70) (b + 199) (b + 205)] ++ (
  mapFuns (b + 199) (b + 202) ++ (
  [itcsSqGF (b + 203)] ++ (
  [itcsEdgeGF (b + 204) (b + 160)] ++ (
  [itcsEdgeT] ++ (
  orbitFuns (b + 205) ++ (
  [itcsFinishF (b + 238) (b + 267) (b + 271) (b + 275) (b + 279)] ++ (
  [itcsRowsF (b + 70) (b + 239)] ++ (
  mapFuns (b + 239) (b + 242) ++ (
  [itcsRowF (b + 243)] ++ (
  [itcsProjectF (b + 244) (b + 263) (b + 95)] ++ (
  [liftLabF (b + 245) (b + 254) 3] ++ (
  [.nil] ++ (
  [shiftAppF (b + 247) (b + 250)] ++ (
  appendFuns (b + 247) ++ (
  mapFuns (b + 250) (b + 253) ++ (
  [addKF] ++ (
  pSplitFuns (b + 254) ++ (
  [itcsGroupMapF (b + 264)] ++ (
  mapFuns (b + 264) (b + 244) ++ (
  filterFuns (b + 267) (b + 270) ++ (
  [itcsRowNE] ++ (
  mapFuns (b + 271) (b + 274) ++ (
  [krFstF] ++ (
  [itcsGroupBuildF (b + 139) (b + 276) (b + 177)] ++ (
  mapFuns (b + 276) (b + 95) ++ (
  mapFuns (b + 279) (b + 282) ++ (
  [itcsOverF (b + 95)])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 20000 in
theorem fc11Conc_length (b : ℕ) : (fc11Conc b).length = 283 := rfl

/-- The indices of the first-rectangle item in its room at `b`. -/
def fc11C1 (b : ℕ) : ItC1Idx where
  f := b + 120
  dat := b + 121
  chk := b + 151
  fnd := b + 156
  ft := b + 159
  swt := b + 160
  sb := b + 163
  gen := b + 164
  sch := b + 180
  cmp := b + 95
  par := b + 185
  rng := b + 70
  mpS := b + 122
  sz := b + 125
  cnt := b + 126
  mpP := b + 131
  pb := b + 134
  flt := b + 135
  kb := b + 138
  inv := b + 139
  al := b + 152
  ct := b + 155
  mpT := b + 165
  trB := b + 168
  mpG := b + 169
  gb := b + 172
  bs := b + 173
  bb := b + 176
  app := b + 177
  mpS' := b + 181
  sb' := b + 184
  mpI := b + 186
  ib := b + 189
  fltI := b + 190
  it := b + 193
  fld := b + 194
  st := b + 197

/-- The query indices. -/
def fc11Q (b : ℕ) : itcsQueryIdx where
  ask := b + 49
  data := b + 50
  colors := b + 51
  gp := b + 52
  fm := b + 53
  fst := b + 56
  group := b + 57
  lc := b + 64
  sw := b + 65
  hv := b + 69
  gr := b + 73
  en := b + 74
  fsm := b + 87
  rng := b + 70
  dom := b + 91
  db := b + 94
  cmp := b + 95
  pull := b + 99
  cb := b + 102
  bit := b + 103
  state := b + 104

/-- The colored-partition indices. -/
def fc11Part (b : ℕ) : ItciIdx where
  c1 := fc11C1 b
  f := b + 105
  fa := b + 106
  all := b + 107
  chk := b + 110
  fg := b + 111
  mpC := b + 112
  cb := b + 115
  fnd := b + 116
  t := b + 119

/-- The rectangle-controller indices; the representation program is `fitRpIdx`. -/
def fc11Rect (b : ℕ) : itcsRectIdx where
  query := fc11Q b
  part := fc11Part b
  rep := fitRpIdx
  f := b + 23
  bal := b + 24
  balB := b + 27
  fiberB := b + 28
  sides := b + 29
  sideB := b + 32
  guard := b + 33
  count := b + 126
  align := b + 34
  fix := b + 35
  fixMap := b + 36
  fixB := b + 39
  fixGen := b + 40
  markW := b + 41
  markR := b + 44
  markWB := b + 47
  markRB := b + 48

/-- The component-table indices. -/
def fc11Comp (b : ℕ) : itcsCompIdx where
  c1 := fc11C1 b
  f := b + 198
  mp := b + 199
  sq := b + 202
  eg := b + 203
  et := b + 204
  orb := b + 205

/-- The source-dispatch indices; the certificate search is `fitRcIdx`. -/
def fc11Src (b : ℕ) : itcsSourceIdx where
  rect := fc11Rect b
  comp := fc11Comp b
  cert := fitRcIdx
  f := b + 1
  front := b + 3
  fiber := b + 4
  find := b + 7
  test := b + 10
  pc := b + 11
  size := b + 12
  baltest := b + 13
  baltestB := b + 16
  imp := b + 17
  min := b + 18
  minB := b + 21
  part := b + 22

/-- The finalizer indices; the normalized-factor primitive is prim `3`. -/
def fc11Fin (b : ℕ) : itcsFinalIdx where
  factor := 3
  f := b + 237
  rows := b + 238
  rng := b + 70
  rowMap := b + 239
  rowB := b + 242
  project := b + 243
  lift := b + 244
  groupMap := b + 263
  generatorMap := b + 264
  compose := b + 95
  shift := b + 245
  split := b + 254
  filter := b + 267
  nonempty := b + 270
  firstMap := b + 271
  firstB := b + 274
  groupBuild := b + 275
  inverse := b + 139
  buildMap := b + 276
  append := b + 177
  overMap := b + 279
  overB := b + 282

/-- **The indices of the first-rectangle item** in its room at `b`. -/
def fc11Ix (b : ℕ) : itcsSojIdx where
  init := b + 0
  step := b + 2
  source := fc11Src b
  finalizer := fc11Fin b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The room of the first-rectangle item holds its table.** -/
theorem fc11_sojOk {P : Program} {b : ℕ} {hfac : NormalizedFactor} (h : P.HasAt b (fc11Conc b))
    (h3 : P.prims[3]? = some (normalizedFactorPrim hfac)) : itcsSojOk P (fc11Ix b) hfac := by
  have h : P.HasAt (b + 0) (fc11Conc b) := h
  unfold fc11Conc at h
  obtain ⟨h_init, h⟩ := fit_peel (N' := 1) h rfl rfl
  obtain ⟨h_srcf, h⟩ := fit_peel (N' := 2) h rfl rfl
  obtain ⟨h_step, h⟩ := fit_peel (N' := 3) h rfl rfl
  obtain ⟨h_front, h⟩ := fit_peel (N' := 4) h rfl rfl
  obtain ⟨h_fiber, h⟩ := fit_peel (N' := 7) h rfl rfl
  obtain ⟨h_find, h⟩ := fit_peel (N' := 10) h rfl rfl
  obtain ⟨h_test, h⟩ := fit_peel (N' := 11) h rfl rfl
  obtain ⟨h_pc, h⟩ := fit_peel (N' := 12) h rfl rfl
  obtain ⟨h_size, h⟩ := fit_peel (N' := 13) h rfl rfl
  obtain ⟨h_baltest, h⟩ := fit_peel (N' := 16) h rfl rfl
  obtain ⟨h_baltestB, h⟩ := fit_peel (N' := 17) h rfl rfl
  obtain ⟨h_imp, h⟩ := fit_peel (N' := 18) h rfl rfl
  obtain ⟨h_min, h⟩ := fit_peel (N' := 21) h rfl rfl
  obtain ⟨h_minB, h⟩ := fit_peel (N' := 22) h rfl rfl
  obtain ⟨h_part, h⟩ := fit_peel (N' := 23) h rfl rfl
  obtain ⟨h_rf, h⟩ := fit_peel (N' := 24) h rfl rfl
  obtain ⟨h_rbal, h⟩ := fit_peel (N' := 27) h rfl rfl
  obtain ⟨h_balB, h⟩ := fit_peel (N' := 28) h rfl rfl
  obtain ⟨h_fiberB, h⟩ := fit_peel (N' := 29) h rfl rfl
  obtain ⟨h_sides, h⟩ := fit_peel (N' := 32) h rfl rfl
  obtain ⟨h_sideB, h⟩ := fit_peel (N' := 33) h rfl rfl
  obtain ⟨h_guard, h⟩ := fit_peel (N' := 34) h rfl rfl
  obtain ⟨h_align, h⟩ := fit_peel (N' := 35) h rfl rfl
  obtain ⟨h_fix, h⟩ := fit_peel (N' := 36) h rfl rfl
  obtain ⟨h_fixMap, h⟩ := fit_peel (N' := 39) h rfl rfl
  obtain ⟨h_fixB, h⟩ := fit_peel (N' := 40) h rfl rfl
  obtain ⟨h_fixGen, h⟩ := fit_peel (N' := 41) h rfl rfl
  obtain ⟨h_markW, h⟩ := fit_peel (N' := 44) h rfl rfl
  obtain ⟨h_markR, h⟩ := fit_peel (N' := 47) h rfl rfl
  obtain ⟨h_markWB, h⟩ := fit_peel (N' := 48) h rfl rfl
  obtain ⟨h_markRB, h⟩ := fit_peel (N' := 49) h rfl rfl
  obtain ⟨h_ask, h⟩ := fit_peel (N' := 50) h rfl rfl
  obtain ⟨h_data, h⟩ := fit_peel (N' := 51) h rfl rfl
  obtain ⟨h_colors, h⟩ := fit_peel (N' := 52) h rfl rfl
  obtain ⟨h_gp, h⟩ := fit_peel (N' := 53) h rfl rfl
  obtain ⟨h_fm, h⟩ := fit_peel (N' := 56) h rfl rfl
  obtain ⟨h_fst, h⟩ := fit_peel (N' := 57) h rfl rfl
  obtain ⟨h_group, h⟩ := fit_peel (N' := 64) h rfl rfl
  obtain ⟨h_lc, h⟩ := fit_peel (N' := 65) h rfl rfl
  obtain ⟨h_sw, h⟩ := fit_peel (N' := 69) h rfl rfl
  obtain ⟨h_hv, h⟩ := fit_peel (N' := 70) h rfl rfl
  obtain ⟨h_rng, h⟩ := fit_peel (N' := 73) h rfl rfl
  obtain ⟨h_gr, h⟩ := fit_peel (N' := 74) h rfl rfl
  obtain ⟨h_en, h⟩ := fit_peel (N' := 87) h rfl rfl
  obtain ⟨h_fsm, h⟩ := fit_peel (N' := 91) h rfl rfl
  obtain ⟨h_dom, h⟩ := fit_peel (N' := 94) h rfl rfl
  obtain ⟨h_db, h⟩ := fit_peel (N' := 95) h rfl rfl
  obtain ⟨h_cmp, h⟩ := fit_peel (N' := 99) h rfl rfl
  obtain ⟨h_pull, h⟩ := fit_peel (N' := 102) h rfl rfl
  obtain ⟨h_cb, h⟩ := fit_peel (N' := 103) h rfl rfl
  obtain ⟨h_bit, h⟩ := fit_peel (N' := 104) h rfl rfl
  obtain ⟨h_state, h⟩ := fit_peel (N' := 105) h rfl rfl
  obtain ⟨h_pf, h⟩ := fit_peel (N' := 106) h rfl rfl
  obtain ⟨h_pfa, h⟩ := fit_peel (N' := 107) h rfl rfl
  obtain ⟨h_pall, h⟩ := fit_peel (N' := 110) h rfl rfl
  obtain ⟨h_pchk, h⟩ := fit_peel (N' := 111) h rfl rfl
  obtain ⟨h_pfg, h⟩ := fit_peel (N' := 112) h rfl rfl
  obtain ⟨h_pmpC, h⟩ := fit_peel (N' := 115) h rfl rfl
  obtain ⟨h_pcb, h⟩ := fit_peel (N' := 116) h rfl rfl
  obtain ⟨h_pfnd, h⟩ := fit_peel (N' := 119) h rfl rfl
  obtain ⟨h_pt, h⟩ := fit_peel (N' := 120) h rfl rfl
  obtain ⟨h_c1f, h⟩ := fit_peel (N' := 121) h rfl rfl
  obtain ⟨h_dat, h⟩ := fit_peel (N' := 122) h rfl rfl
  obtain ⟨h_mpS, h⟩ := fit_peel (N' := 125) h rfl rfl
  obtain ⟨h_sz, h⟩ := fit_peel (N' := 126) h rfl rfl
  obtain ⟨h_cnt, h⟩ := fit_peel (N' := 131) h rfl rfl
  obtain ⟨h_mpP, h⟩ := fit_peel (N' := 134) h rfl rfl
  obtain ⟨h_pb, h⟩ := fit_peel (N' := 135) h rfl rfl
  obtain ⟨h_flt, h⟩ := fit_peel (N' := 138) h rfl rfl
  obtain ⟨h_kb, h⟩ := fit_peel (N' := 139) h rfl rfl
  obtain ⟨h_inv, h⟩ := fit_peel (N' := 151) h rfl rfl
  obtain ⟨h_chk, h⟩ := fit_peel (N' := 152) h rfl rfl
  obtain ⟨h_al, h⟩ := fit_peel (N' := 155) h rfl rfl
  obtain ⟨h_ct, h⟩ := fit_peel (N' := 156) h rfl rfl
  obtain ⟨h_fnd, h⟩ := fit_peel (N' := 159) h rfl rfl
  obtain ⟨h_ft, h⟩ := fit_peel (N' := 160) h rfl rfl
  obtain ⟨h_swt, h⟩ := fit_peel (N' := 163) h rfl rfl
  obtain ⟨h_sb, h⟩ := fit_peel (N' := 164) h rfl rfl
  obtain ⟨h_gen, h⟩ := fit_peel (N' := 165) h rfl rfl
  obtain ⟨h_mpT, h⟩ := fit_peel (N' := 168) h rfl rfl
  obtain ⟨h_trB, h⟩ := fit_peel (N' := 169) h rfl rfl
  obtain ⟨h_mpG, h⟩ := fit_peel (N' := 172) h rfl rfl
  obtain ⟨h_gb, h⟩ := fit_peel (N' := 173) h rfl rfl
  obtain ⟨h_bs, h⟩ := fit_peel (N' := 176) h rfl rfl
  obtain ⟨h_bb, h⟩ := fit_peel (N' := 177) h rfl rfl
  obtain ⟨h_app, h⟩ := fit_peel (N' := 180) h rfl rfl
  obtain ⟨h_sch, h⟩ := fit_peel (N' := 181) h rfl rfl
  obtain ⟨h_mpS2, h⟩ := fit_peel (N' := 184) h rfl rfl
  obtain ⟨h_sb2, h⟩ := fit_peel (N' := 185) h rfl rfl
  obtain ⟨h_par, h⟩ := fit_peel (N' := 186) h rfl rfl
  obtain ⟨h_mpI, h⟩ := fit_peel (N' := 189) h rfl rfl
  obtain ⟨h_ib, h⟩ := fit_peel (N' := 190) h rfl rfl
  obtain ⟨h_fltI, h⟩ := fit_peel (N' := 193) h rfl rfl
  obtain ⟨h_it, h⟩ := fit_peel (N' := 194) h rfl rfl
  obtain ⟨h_fld, h⟩ := fit_peel (N' := 197) h rfl rfl
  obtain ⟨h_st, h⟩ := fit_peel (N' := 198) h rfl rfl
  obtain ⟨h_compf, h⟩ := fit_peel (N' := 199) h rfl rfl
  obtain ⟨h_cmpmp, h⟩ := fit_peel (N' := 202) h rfl rfl
  obtain ⟨h_sq, h⟩ := fit_peel (N' := 203) h rfl rfl
  obtain ⟨h_eg, h⟩ := fit_peel (N' := 204) h rfl rfl
  obtain ⟨h_et, h⟩ := fit_peel (N' := 205) h rfl rfl
  obtain ⟨h_orb, h⟩ := fit_peel (N' := 237) h rfl rfl
  obtain ⟨h_ff, h⟩ := fit_peel (N' := 238) h rfl rfl
  obtain ⟨h_rows, h⟩ := fit_peel (N' := 239) h rfl rfl
  obtain ⟨h_rowMap, h⟩ := fit_peel (N' := 242) h rfl rfl
  obtain ⟨h_rowB, h⟩ := fit_peel (N' := 243) h rfl rfl
  obtain ⟨h_project, h⟩ := fit_peel (N' := 244) h rfl rfl
  obtain ⟨h_lift, h⟩ := fit_peel (N' := 245) h rfl rfl
  obtain ⟨h_shift, h⟩ := fit_peel (N' := 246) h rfl rfl
  obtain ⟨h_shApp, h⟩ := fit_peel (N' := 247) h rfl rfl
  obtain ⟨h_shAppend, h⟩ := fit_peel (N' := 250) h rfl rfl
  obtain ⟨h_shAdd, h⟩ := fit_peel (N' := 253) h rfl rfl
  obtain ⟨h_shK, h⟩ := fit_peel (N' := 254) h rfl rfl
  obtain ⟨h_split, h⟩ := fit_peel (N' := 263) h rfl rfl
  obtain ⟨h_groupMap, h⟩ := fit_peel (N' := 264) h rfl rfl
  obtain ⟨h_generatorMap, h⟩ := fit_peel (N' := 267) h rfl rfl
  obtain ⟨h_filter, h⟩ := fit_peel (N' := 270) h rfl rfl
  obtain ⟨h_nonempty, h⟩ := fit_peel (N' := 271) h rfl rfl
  obtain ⟨h_firstMap, h⟩ := fit_peel (N' := 274) h rfl rfl
  obtain ⟨h_firstB, h⟩ := fit_peel (N' := 275) h rfl rfl
  obtain ⟨h_groupBuild, h⟩ := fit_peel (N' := 276) h rfl rfl
  obtain ⟨h_buildMap, h⟩ := fit_peel (N' := 279) h rfl rfl
  obtain ⟨h_overMap, h⟩ := fit_peel (N' := 282) h rfl rfl
  have h_overB := h
  have hc1 : ItC1Ok P (fc11C1 b) := { f := h_c1f.single, rng := h_rng, dat := h_dat.single, mpS := h_mpS, sz := h_sz.single, cnt := h_cnt, mpP := h_mpP, pb := h_pb.single, flt := h_flt, kb := h_kb.single, inv := h_inv, chk := h_chk.single, al := h_al, ct := h_ct.single, fnd := h_fnd, ft := h_ft.single, swt := h_swt, sb := h_sb.single, gen := h_gen.single, mpT := h_mpT, trB := h_trB.single, mpG := h_mpG, gb := h_gb.single, bs := h_bs, bb := h_bb.single, app := h_app, sch := h_sch.single, mpS' := h_mpS2, sb' := h_sb2.single, cmp := h_cmp, par := h_par.single, mpI := h_mpI, ib := h_ib.single, fltI := h_fltI, it := h_it.single, fld := h_fld, st := h_st.single }
  have hq : itcsQueryOk P (fc11Q b) := { ask := h_ask.single, data := h_data.single, colors := h_colors.single, gp := h_gp.single, fm := h_fm, fst := h_fst.single, group := h_group, lc := h_lc.single, sw := h_sw, hv := h_hv.single, rng := h_rng, gr := h_gr.single, en := h_en, fsm := h_fsm, dom := h_dom, db := h_db.single, cmp := h_cmp, pull := h_pull, cb := h_cb.single, bit := h_bit.single, state := h_state.single }
  have hpart : ItciOk P (fc11Part b) := { c1 := hc1, f := h_pf.single, fa := h_pfa.single, all := h_pall, chk := h_pchk.single, fg := h_pfg.single, mpC := h_pmpC, cb := h_pcb.single, fnd := h_pfnd, t := h_pt.single }
  have hrect : itcsRectOk P (fc11Rect b) := { query := hq, part := hpart, body := h_rf.single, bal := h_rbal, balB := h_balB.single, fiberB := h_fiberB.single, sides := h_sides, sideB := h_sideB.single, guard := h_guard.single, count := h_cnt, align := h_align.single, fix := h_fix.single, fixMap := h_fixMap, fixB := h_fixB.single, fixGen := h_fixGen.single, markW := h_markW, markR := h_markR, markWB := h_markWB.single, markRB := h_markRB.single }
  have hcomp : itcsCompOk P (fc11Comp b) := { c1 := hc1, f := h_compf.single, mp := h_cmpmp, sq := h_sq.single, eg := h_eg.single, et := h_et.single, orb := h_orb }
  have hsrc : itcsSourceOk P (fc11Src b) := { rect := hrect, comp := hcomp, body := h_srcf.single, front := h_front.single, fiber := h_fiber, find := h_find, test := h_test.single, pc := h_pc.single, size := h_size.single, baltest := h_baltest, baltestB := h_baltestB.single, imp := h_imp.single, min := h_min, minB := h_minB.single, part := h_part.single }
  have hsh : ShiftAt P (b + 245) := ⟨h_shApp.single, h_shAppend, h_shAdd, h_shK.single⟩
  have hfin : itcsFinalOk P (fc11Fin b) hfac := { factor := h3, shift := hsh, body := h_ff.single, rows := h_rows.single, rng := h_rng, rowMap := h_rowMap, rowB := h_rowB.single, project := h_project.single, lift := h_lift.single, split := h_split, groupMap := h_groupMap.single, generatorMap := h_generatorMap, compose := h_cmp, filter := h_filter, nonempty := h_nonempty.single, firstMap := h_firstMap, firstB := h_firstB.single, groupBuild := h_groupBuild.single, inverse := h_inv, buildMap := h_buildMap, append := h_app, overMap := h_overMap, overB := h_overB.single }
  exact { init := h_init.single, step := h_step.single, source := hsrc, finalizer := hfin }

end GI.Impl
