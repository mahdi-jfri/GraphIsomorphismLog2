import Workspace.Impl.AggItemOKStr
import Workspace.Impl.AggItemOKC1
import Workspace.Impl.AggItemHvCase
import Workspace.Impl.AggRectCertS
import Workspace.Impl.LayoutAsm

/-!
# The concrete part of the items' list

The items' helper list `itF` sits at `fagItIdx = asb 601000` (`FinLayoutAgg.lean`). Its first
`fitHvOff = 10000` entries hold the programs of the items that are written:
`fitConc c` at base `c` (298 functions, `length_fitConc`). The remaining parts are abstract lists
placed by `FinLayoutItemsOK.lean`: the init program of Case 2a at `c + fitHvOff`, the programs of
Cases 2b and 3 at `c + fitC23Off` (init at offset `0`, branch step at offset `1`), and the
rectangle representation program at `c + fitRpOff`.

`fitConc c` is one function or one library module after the other, with no padding, in this
order (offsets from `c`):

* `0`–`27`: the structure step (`itS_strOK`): `itStrF`, `itColF`, `itTsF`, `itTvF`, `stRefF`
  (refinement at primitive `19`), the case test `itCaseF`, `acpCaseF` and its callees (with
  **PointwiseStab** at `0` and **GroupOrder** at `5`), `itGrpF`, `itSndF`, `itSrcF`, `itDomF`,
  `itS2bF`, the Case 3 source search `stDSrcF`, `stDSrcPF` and the Case 3 test `stDesF` with
  its callees (`stDHitF`, `stDHit2F`, `stDSplitF`, …);
* `28`–`37`: the run (`ItSRunAt`): `itSRunF`, the dispatchers `itSDispF` of the init programs
  (`29`) and of the branch steps (`30`), `runBody`, `cpLoopBody`, the moves and `itSFacF`;
* `38`–`58`: Case 1 (`itS_c1_caseOK`): init `itSC1IF` at `38`, branch step `itSC1F` at `39`,
  and the single functions of `ItC1Ok`;
* `59`–`60`: the branch step `itHvBF` of Case 2a and its piece program `itHvPcF`;
* `61`–`70`: the certificate search `rcCertF` (at `61`) and the single functions of `RcCertOk`;
* `71`–`297`: the library modules, each once; a module that several programs call (`rangeFuns`
  at `74`, `countFuns` at `153`, `appendFuns` at `172`, `orbitFuns` at `115`, `composeFuns` at
  `241`, …) is shared.

`FitAt P c` lists every entry with its index, and `fit_at` gets it from `P.HasAt c (fitConc c)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang

set_option maxRecDepth 100000

/-- The offset of the init program of Case 2a in the items' list. -/
def fitHvOff : ℕ := 10000

/-- The offset of the programs of Cases 2b and 3 in the items' list. -/
def fitC23Off : ℕ := 100000

/-- The offset of the rectangle representation program in the items' list. -/
def fitRpOff : ℕ := 300000

/-- The room of the items' list. -/
def fitRoom : ℕ := 400000

/-! ### The lengths of the library modules -/

theorem fit_len_allFuns (b f : ℕ) : (allFuns b f).length = 3 := rfl

theorem fit_len_anyFuns (b f : ℕ) : (anyFuns b f).length = 3 := rfl

theorem fit_len_appendFuns (b : ℕ) : (appendFuns b).length = 3 := rfl

theorem fit_len_composeFuns (b : ℕ) : (composeFuns b).length = 4 := rfl

theorem fit_len_countFuns (b : ℕ) : (countFuns b).length = 5 := rfl

theorem fit_len_eqNatsFuns (b : ℕ) : (eqNatsFuns b).length = 3 := rfl

theorem fit_len_factFuns (b : ℕ) : (factFuns b).length = 3 := rfl

theorem fit_len_filterFuns (b f : ℕ) : (filterFuns b f).length = 3 := rfl

theorem fit_len_findEqFuns (b : ℕ) : (findEqFuns b).length = 4 := rfl

theorem fit_len_findFuns (b f : ℕ) : (findFuns b f).length = 3 := rfl

theorem fit_len_foldlFuns (b f : ℕ) : (foldlFuns b f).length = 3 := rfl

theorem fit_len_gatherFuns (b : ℕ) : (gatherFuns b).length = 4 := rfl

theorem fit_len_invFuns (b : ℕ) : (invFuns b).length = 12 := rfl

theorem fit_len_mapFuns (b f : ℕ) : (mapFuns b f).length = 3 := rfl

theorem fit_len_orbitFuns (b : ℕ) : (orbitFuns b).length = 32 := rfl

theorem fit_len_pstabFuns (b j : ℕ) : (pstabFuns b j).length = 8 := rfl

theorem fit_len_rangeFuns (b : ℕ) : (rangeFuns b).length = 3 := rfl

theorem fit_len_replicateFuns (b : ℕ) : (replicateFuns b).length = 3 := rfl

theorem fit_len_stColsFuns (b f : ℕ) : (stColsFuns b f).length = 8 := rfl

theorem fit_len_stDDecFuns (b : ℕ) : (stDDecFuns b).length = 3 := rfl

theorem fit_len_stDHorFuns (b : ℕ) : (stDHorFuns b).length = 3 := rfl

theorem fit_len_stDPowFuns (b : ℕ) : (stDPowFuns b).length = 3 := rfl

theorem fit_len_stRelFuns (b : ℕ) : (stRelFuns b).length = 21 := rfl

/-! ### The list -/

/-- **The concrete part of the items' list** at base `c` (see the module docstring). -/
noncomputable def fitConc (c : ℕ) : List Expr :=
  [itStrF (c + 1) (c + 5) (c + 12)] ++
  ([itColF (c + 2) (c + 83) (c + 4) P₀.κ] ++
  ([itTsF (c + 71) (c + 74) (c + 77)] ++
  ([itTvF (c + 80)] ++
  ([stRefF (c + 112) 19] ++
  ([itCaseF (c + 6) (c + 10)] ++
  ([acpCaseF (c + 115) (c + 74) (c + 147) (c + 150) (c + 9)] ++
  ([acpDomF (c + 153)] ++
  ([acpSuppF (c + 153)] ++
  ([acpGiantF (c + 158) (c + 166) 5] ++
  ([itGrpF (c + 74) (c + 169) (c + 172)] ++
  ([itSndF] ++
  ([itSrcF (c + 10) (c + 13) (c + 14) (c + 15) (c + 112) P₀.κ] ++
  ([itDomF (c + 115) (c + 74) (c + 147)] ++
  ([itS2bF (c + 172) (c + 112) P₀.κ] ++
  ([stDSrcF (c + 71) (c + 175) (c + 74) (c + 80)] ++
  ([stDSrcPF (c + 17) (c + 80)] ++
  ([stDesF (c + 187) (c + 74) (c + 23) (c + 184) (c + 27) (c + 25)] ++
  ([stDHitF (c + 19) (c + 23)] ++
  ([stDHit2F (c + 184) (c + 74) (c + 20)] ++
  ([stDSplitF (c + 190) (c + 193) (c + 196) (c + 74) (c + 25)] ++
  ([stDRefF] ++
  ([stDDifF (c + 21) (c + 25)] ++
  ([stDVMapF (c + 181) (c + 74)] ++
  ([stDVF (c + 25)] ++
  ([stDColF (c + 178)] ++
  ([stDDomF (c + 27)] ++
  ([stDDomVF (c + 153)] ++
  ([itSRunF (c + 2) (c + 29) (c + 31)] ++
  ([itSDispF (c + 38) (c + fitHvOff) (c + fitC23Off)] ++
  ([itSDispF (c + 39) (c + 59) (c + (fitC23Off + 1))] ++
  ([runBody asmF (c + 31) (c + 32)] ++
  ([cpLoopBody (c + 32) (c + 33)] ++
  ([itSMvF (c + 34) (c + 35) (c + 36)] ++
  ([itSM0F] ++
  ([itSM1F (c + 30) (c + 37)] ++
  ([itSM3F] ++
  ([itSFacF (c + 172)] ++
  ([itSC1IF] ++
  ([itSC1F (c + 10) (c + 115) (c + 40)] ++
  ([itC1F (c + 41) (c + 45) (c + 223) (c + 226) (c + 49) (c + 53) (c + 241) (c + 55)] ++
  ([itDatF (c + 74) (c + 199) (c + 202) (c + 208)] ++
  ([itSzB (c + 153)] ++
  ([itPosB (c + 205)] ++
  ([itKeyB] ++
  ([itChkF (c + 74) (c + 220)] ++
  ([itCntT (c + 153)] ++
  ([itFixT] ++
  ([itSwB] ++
  ([itGensF (c + 229) (c + 74) (c + 232) (c + 172)] ++
  ([itTrB (c + 226)] ++
  ([itGenB (c + 235)] ++
  ([itBsB] ++
  ([itSchF (c + 74) (c + 238)] ++
  ([itSchB (c + 55) (c + 241)] ++
  ([itParF (c + 74) (c + 245) (c + 251)] ++
  ([itInvB (c + 248)] ++
  ([itInvT] ++
  ([itParS] ++
  ([itHvBF (c + 60)] ++
  ([itHvPcF (c + 241) (c + 172)] ++
  ([rcCertF (c + 254) (c + 74) (c + 257) (c + 264) (c + 268)] ++
  ([rcDiagT] ++
  ([rcDRowF (c + 260)] ++
  ([rcCandF (c + 271) (c + 74) (c + 274) (c + 67)] ++
  ([rcEqT] ++
  ([rcBRowF (c + 277)] ++
  ([rcCondF (c + 280) (c + 283) (c + 74) (c + 289) (c + 153)] ++
  ([rcColDegF (c + 153) (c + 286)] ++
  ([rcGetT] ++
  ([rcTwT (c + 292)] ++
  ((stDPowFuns (c + 71)) ++
  ((rangeFuns (c + 74)) ++
  ((mapFuns (c + 77) (c + 3)) ++
  ((stDDecFuns (c + 80)) ++
  ((stColsFuns (c + 83) (c + 91)) ++
  ((stRelFuns (c + 91)) ++
  ((replicateFuns (c + 112)) ++
  ((orbitFuns (c + 115)) ++
  ((filterFuns (c + 147) (c + 7)) ++
  ((filterFuns (c + 150) (c + 8)) ++
  ((countFuns (c + 153)) ++
  ((pstabFuns (c + 158) 0) ++
  ((factFuns (c + 166)) ++
  ((mapFuns (c + 169) (c + 11)) ++
  ((appendFuns (c + 172)) ++
  ((findFuns (c + 175) (c + 16)) ++
  ((stDHorFuns (c + 178)) ++
  ((mapFuns (c + 181) (c + 24)) ++
  ((anyFuns (c + 184) (c + 26)) ++
  ((findFuns (c + 187) (c + 18)) ++
  ((findFuns (c + 190) (c + 26)) ++
  ((findFuns (c + 193) (c + 21)) ++
  ((anyFuns (c + 196) (c + 22)) ++
  ((mapFuns (c + 199) (c + 42)) ++
  ((mapFuns (c + 202) (c + 43)) ++
  ((filterFuns (c + 205) (c + 44)) ++
  ((invFuns (c + 208)) ++
  ((allFuns (c + 220) (c + 46)) ++
  ((findFuns (c + 223) (c + 47)) ++
  ((mapFuns (c + 226) (c + 48)) ++
  ((mapFuns (c + 229) (c + 50)) ++
  ((mapFuns (c + 232) (c + 51)) ++
  ((mapFuns (c + 235) (c + 52)) ++
  ((mapFuns (c + 238) (c + 54)) ++
  ((composeFuns (c + 241)) ++
  ((mapFuns (c + 245) (c + 56)) ++
  ((filterFuns (c + 248) (c + 57)) ++
  ((foldlFuns (c + 251) (c + 58)) ++
  ((filterFuns (c + 254) (c + 62)) ++
  ((mapFuns (c + 257) (c + 63)) ++
  ((gatherFuns (c + 260)) ++
  ((findEqFuns (c + 264)) ++
  ((findFuns (c + 268) (c + 64)) ++
  ((filterFuns (c + 271) (c + 65)) ++
  ((mapFuns (c + 274) (c + 66)) ++
  ((mapFuns (c + 277) (c + 65)) ++
  ((mapFuns (c + 280) (c + 153)) ++
  ((mapFuns (c + 283) (c + 68)) ++
  ((mapFuns (c + 286) (c + 69)) ++
  ((allFuns (c + 289) (c + 70)) ++
  ((filterFuns (c + 292) (c + 295)) ++
  ((eqNatsFuns (c + 295))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem length_fitConc (c : ℕ) : (fitConc c).length = 298 := by
  simp only [fitConc, List.length_append, List.length_cons, List.length_nil, fit_len_allFuns, fit_len_anyFuns, fit_len_appendFuns, fit_len_composeFuns, fit_len_countFuns, fit_len_eqNatsFuns, fit_len_factFuns, fit_len_filterFuns, fit_len_findEqFuns, fit_len_findFuns, fit_len_foldlFuns, fit_len_gatherFuns, fit_len_invFuns, fit_len_mapFuns, fit_len_orbitFuns, fit_len_pstabFuns, fit_len_rangeFuns, fit_len_replicateFuns, fit_len_stColsFuns, fit_len_stDDecFuns, fit_len_stDHorFuns, fit_len_stDPowFuns, fit_len_stRelFuns]

theorem length_fitConc_le (c : ℕ) : (fitConc c).length ≤ fitHvOff := by
  rw [length_fitConc]; unfold fitHvOff; omega

/-! ### The entries -/

/-- **The entries of `fitConc c`** in a program `P`, each at its index. -/
structure FitAt (P : Program) (c : ℕ) : Prop where
  str : P.funs[c + 0]? = some (itStrF (c + 1) (c + 5) (c + 12))
  col : P.funs[c + 1]? = some (itColF (c + 2) (c + 83) (c + 4) P₀.κ)
  ts : P.funs[c + 2]? = some (itTsF (c + 71) (c + 74) (c + 77))
  tv : P.funs[c + 3]? = some (itTvF (c + 80))
  fr : P.funs[c + 4]? = some (stRefF (c + 112) 19)
  cse : P.funs[c + 5]? = some (itCaseF (c + 6) (c + 10))
  acp : P.funs[c + 6]? = some (acpCaseF (c + 115) (c + 74) (c + 147) (c + 150) (c + 9))
  pd : P.funs[c + 7]? = some (acpDomF (c + 153))
  ps : P.funs[c + 8]? = some (acpSuppF (c + 153))
  g : P.funs[c + 9]? = some (acpGiantF (c + 158) (c + 166) 5)
  grp : P.funs[c + 10]? = some (itGrpF (c + 74) (c + 169) (c + 172))
  sf : P.funs[c + 11]? = some (itSndF)
  sp : P.funs[c + 12]? = some (itSrcF (c + 10) (c + 13) (c + 14) (c + 15) (c + 112) P₀.κ)
  dom : P.funs[c + 13]? = some (itDomF (c + 115) (c + 74) (c + 147))
  s2b : P.funs[c + 14]? = some (itS2bF (c + 172) (c + 112) P₀.κ)
  s3 : P.funs[c + 15]? = some (stDSrcF (c + 71) (c + 175) (c + 74) (c + 80))
  spp : P.funs[c + 16]? = some (stDSrcPF (c + 17) (c + 80))
  des : P.funs[c + 17]? = some (stDesF (c + 187) (c + 74) (c + 23) (c + 184) (c + 27) (c + 25))
  ht : P.funs[c + 18]? = some (stDHitF (c + 19) (c + 23))
  h2 : P.funs[c + 19]? = some (stDHit2F (c + 184) (c + 74) (c + 20))
  spl : P.funs[c + 20]? = some (stDSplitF (c + 190) (c + 193) (c + 196) (c + 74) (c + 25))
  rf : P.funs[c + 21]? = some (stDRefF)
  df : P.funs[c + 22]? = some (stDDifF (c + 21) (c + 25))
  vm : P.funs[c + 23]? = some (stDVMapF (c + 181) (c + 74))
  vf : P.funs[c + 24]? = some (stDVF (c + 25))
  cf : P.funs[c + 25]? = some (stDColF (c + 178))
  dv : P.funs[c + 26]? = some (stDDomF (c + 27))
  dvv : P.funs[c + 27]? = some (stDDomVF (c + 153))
  run : P.funs[c + 28]? = some (itSRunF (c + 2) (c + 29) (c + 31))
  di0 : P.funs[c + 29]? = some (itSDispF (c + 38) (c + fitHvOff) (c + fitC23Off))
  db : P.funs[c + 30]? = some (itSDispF (c + 39) (c + 59) (c + (fitC23Off + 1)))
  drun : P.funs[c + 31]? = some (runBody asmF (c + 31) (c + 32))
  dloop : P.funs[c + 32]? = some (cpLoopBody (c + 32) (c + 33))
  mv : P.funs[c + 33]? = some (itSMvF (c + 34) (c + 35) (c + 36))
  m0 : P.funs[c + 34]? = some (itSM0F)
  m1 : P.funs[c + 35]? = some (itSM1F (c + 30) (c + 37))
  m3 : P.funs[c + 36]? = some (itSM3F)
  facc : P.funs[c + 37]? = some (itSFacF (c + 172))
  i1 : P.funs[c + 38]? = some (itSC1IF)
  b1 : P.funs[c + 39]? = some (itSC1F (c + 10) (c + 115) (c + 40))
  c1 : P.funs[c + 40]? = some (itC1F (c + 41) (c + 45) (c + 223) (c + 226) (c + 49) (c + 53) (c + 241) (c + 55))
  dat : P.funs[c + 41]? = some (itDatF (c + 74) (c + 199) (c + 202) (c + 208))
  sz : P.funs[c + 42]? = some (itSzB (c + 153))
  pb : P.funs[c + 43]? = some (itPosB (c + 205))
  kb : P.funs[c + 44]? = some (itKeyB)
  chk : P.funs[c + 45]? = some (itChkF (c + 74) (c + 220))
  ct : P.funs[c + 46]? = some (itCntT (c + 153))
  ft : P.funs[c + 47]? = some (itFixT)
  sb : P.funs[c + 48]? = some (itSwB)
  gen : P.funs[c + 49]? = some (itGensF (c + 229) (c + 74) (c + 232) (c + 172))
  trB : P.funs[c + 50]? = some (itTrB (c + 226))
  gb : P.funs[c + 51]? = some (itGenB (c + 235))
  bb : P.funs[c + 52]? = some (itBsB)
  sch : P.funs[c + 53]? = some (itSchF (c + 74) (c + 238))
  sb2 : P.funs[c + 54]? = some (itSchB (c + 55) (c + 241))
  par : P.funs[c + 55]? = some (itParF (c + 74) (c + 245) (c + 251))
  ib : P.funs[c + 56]? = some (itInvB (c + 248))
  it : P.funs[c + 57]? = some (itInvT)
  st : P.funs[c + 58]? = some (itParS)
  b2 : P.funs[c + 59]? = some (itHvBF (c + 60))
  pc : P.funs[c + 60]? = some (itHvPcF (c + 241) (c + 172))
  rc : P.funs[c + 61]? = some (rcCertF (c + 254) (c + 74) (c + 257) (c + 264) (c + 268))
  dg : P.funs[c + 62]? = some (rcDiagT)
  dr : P.funs[c + 63]? = some (rcDRowF (c + 260))
  cand : P.funs[c + 64]? = some (rcCandF (c + 271) (c + 74) (c + 274) (c + 67))
  et : P.funs[c + 65]? = some (rcEqT)
  br : P.funs[c + 66]? = some (rcBRowF (c + 277))
  cond : P.funs[c + 67]? = some (rcCondF (c + 280) (c + 283) (c + 74) (c + 289) (c + 153))
  cd : P.funs[c + 68]? = some (rcColDegF (c + 153) (c + 286))
  gt : P.funs[c + 69]? = some (rcGetT)
  tw : P.funs[c + 70]? = some (rcTwT (c + 292))
  pw : P.HasAt (c + 71) (stDPowFuns (c + 71))
  rb : P.HasAt (c + 74) (rangeFuns (c + 74))
  mp : P.HasAt (c + 77) (mapFuns (c + 77) (c + 3))
  dc : P.HasAt (c + 80) (stDDecFuns (c + 80))
  bc : P.HasAt (c + 83) (stColsFuns (c + 83) (c + 91))
  brel : P.HasAt (c + 91) (stRelFuns (c + 91))
  brep : P.HasAt (c + 112) (replicateFuns (c + 112))
  orb : P.HasAt (c + 115) (orbitFuns (c + 115))
  fd : P.HasAt (c + 147) (filterFuns (c + 147) (c + 7))
  fs : P.HasAt (c + 150) (filterFuns (c + 150) (c + 8))
  cnt : P.HasAt (c + 153) (countFuns (c + 153))
  pst : P.HasAt (c + 158) (pstabFuns (c + 158) 0)
  fac : P.HasAt (c + 166) (factFuns (c + 166))
  mpsf : P.HasAt (c + 169) (mapFuns (c + 169) (c + 11))
  app : P.HasAt (c + 172) (appendFuns (c + 172))
  fs3 : P.HasAt (c + 175) (findFuns (c + 175) (c + 16))
  h : P.HasAt (c + 178) (stDHorFuns (c + 178))
  mb : P.HasAt (c + 181) (mapFuns (c + 181) (c + 24))
  ad : P.HasAt (c + 184) (anyFuns (c + 184) (c + 26))
  fh : P.HasAt (c + 187) (findFuns (c + 187) (c + 18))
  fdd : P.HasAt (c + 190) (findFuns (c + 190) (c + 26))
  frr : P.HasAt (c + 193) (findFuns (c + 193) (c + 21))
  add : P.HasAt (c + 196) (anyFuns (c + 196) (c + 22))
  mpS : P.HasAt (c + 199) (mapFuns (c + 199) (c + 42))
  mpP : P.HasAt (c + 202) (mapFuns (c + 202) (c + 43))
  flt : P.HasAt (c + 205) (filterFuns (c + 205) (c + 44))
  inv : P.HasAt (c + 208) (invFuns (c + 208))
  al : P.HasAt (c + 220) (allFuns (c + 220) (c + 46))
  fnd : P.HasAt (c + 223) (findFuns (c + 223) (c + 47))
  swt : P.HasAt (c + 226) (mapFuns (c + 226) (c + 48))
  mpT : P.HasAt (c + 229) (mapFuns (c + 229) (c + 50))
  mpG : P.HasAt (c + 232) (mapFuns (c + 232) (c + 51))
  bs : P.HasAt (c + 235) (mapFuns (c + 235) (c + 52))
  mpS2 : P.HasAt (c + 238) (mapFuns (c + 238) (c + 54))
  cmp : P.HasAt (c + 241) (composeFuns (c + 241))
  mpI : P.HasAt (c + 245) (mapFuns (c + 245) (c + 56))
  fltI : P.HasAt (c + 248) (filterFuns (c + 248) (c + 57))
  fld : P.HasAt (c + 251) (foldlFuns (c + 251) (c + 58))
  flt2 : P.HasAt (c + 254) (filterFuns (c + 254) (c + 62))
  md : P.HasAt (c + 257) (mapFuns (c + 257) (c + 63))
  gth : P.HasAt (c + 260) (gatherFuns (c + 260))
  fq : P.HasAt (c + 264) (findEqFuns (c + 264))
  fnd2 : P.HasAt (c + 268) (findFuns (c + 268) (c + 64))
  flt3 : P.HasAt (c + 271) (filterFuns (c + 271) (c + 65))
  mb2 : P.HasAt (c + 274) (mapFuns (c + 274) (c + 66))
  mbe : P.HasAt (c + 277) (mapFuns (c + 277) (c + 65))
  mc : P.HasAt (c + 280) (mapFuns (c + 280) (c + 153))
  mcd : P.HasAt (c + 283) (mapFuns (c + 283) (c + 68))
  mg : P.HasAt (c + 286) (mapFuns (c + 286) (c + 69))
  al2 : P.HasAt (c + 289) (allFuns (c + 289) (c + 70))
  fe : P.HasAt (c + 292) (filterFuns (c + 292) (c + 295))
  en : P.HasAt (c + 295) (eqNatsFuns (c + 295))

/-- Split off the first block of a list at base `b + N`. -/
theorem fit_peel {P : Program} {b N n N' : ℕ} {A B : List Expr} (h : P.HasAt (b + N) (A ++ B))
    (hl : A.length = n) (hN : N + n = N') : P.HasAt (b + N) A ∧ P.HasAt (b + N') B := by
  refine ⟨h.left, ?_⟩
  have h2 := h.right
  rw [hl, Nat.add_assoc, hN] at h2
  exact h2

set_option maxHeartbeats 4000000 in
/-- **The entries of `fitConc c`** from its place. -/
theorem fit_at {P : Program} {c : ℕ} (h : P.HasAt c (fitConc c)) : FitAt P c := by
  have h : P.HasAt (c + 0) (fitConc c) := h
  unfold fitConc at h
  obtain ⟨x_str, h⟩ := fit_peel (N' := 1) h rfl rfl
  obtain ⟨x_col, h⟩ := fit_peel (N' := 2) h rfl rfl
  obtain ⟨x_ts, h⟩ := fit_peel (N' := 3) h rfl rfl
  obtain ⟨x_tv, h⟩ := fit_peel (N' := 4) h rfl rfl
  obtain ⟨x_fr, h⟩ := fit_peel (N' := 5) h rfl rfl
  obtain ⟨x_cse, h⟩ := fit_peel (N' := 6) h rfl rfl
  obtain ⟨x_acp, h⟩ := fit_peel (N' := 7) h rfl rfl
  obtain ⟨x_pd, h⟩ := fit_peel (N' := 8) h rfl rfl
  obtain ⟨x_ps, h⟩ := fit_peel (N' := 9) h rfl rfl
  obtain ⟨x_g, h⟩ := fit_peel (N' := 10) h rfl rfl
  obtain ⟨x_grp, h⟩ := fit_peel (N' := 11) h rfl rfl
  obtain ⟨x_sf, h⟩ := fit_peel (N' := 12) h rfl rfl
  obtain ⟨x_sp, h⟩ := fit_peel (N' := 13) h rfl rfl
  obtain ⟨x_dom, h⟩ := fit_peel (N' := 14) h rfl rfl
  obtain ⟨x_s2b, h⟩ := fit_peel (N' := 15) h rfl rfl
  obtain ⟨x_s3, h⟩ := fit_peel (N' := 16) h rfl rfl
  obtain ⟨x_spp, h⟩ := fit_peel (N' := 17) h rfl rfl
  obtain ⟨x_des, h⟩ := fit_peel (N' := 18) h rfl rfl
  obtain ⟨x_ht, h⟩ := fit_peel (N' := 19) h rfl rfl
  obtain ⟨x_h2, h⟩ := fit_peel (N' := 20) h rfl rfl
  obtain ⟨x_spl, h⟩ := fit_peel (N' := 21) h rfl rfl
  obtain ⟨x_rf, h⟩ := fit_peel (N' := 22) h rfl rfl
  obtain ⟨x_df, h⟩ := fit_peel (N' := 23) h rfl rfl
  obtain ⟨x_vm, h⟩ := fit_peel (N' := 24) h rfl rfl
  obtain ⟨x_vf, h⟩ := fit_peel (N' := 25) h rfl rfl
  obtain ⟨x_cf, h⟩ := fit_peel (N' := 26) h rfl rfl
  obtain ⟨x_dv, h⟩ := fit_peel (N' := 27) h rfl rfl
  obtain ⟨x_dvv, h⟩ := fit_peel (N' := 28) h rfl rfl
  obtain ⟨x_run, h⟩ := fit_peel (N' := 29) h rfl rfl
  obtain ⟨x_di0, h⟩ := fit_peel (N' := 30) h rfl rfl
  obtain ⟨x_db, h⟩ := fit_peel (N' := 31) h rfl rfl
  obtain ⟨x_drun, h⟩ := fit_peel (N' := 32) h rfl rfl
  obtain ⟨x_dloop, h⟩ := fit_peel (N' := 33) h rfl rfl
  obtain ⟨x_mv, h⟩ := fit_peel (N' := 34) h rfl rfl
  obtain ⟨x_m0, h⟩ := fit_peel (N' := 35) h rfl rfl
  obtain ⟨x_m1, h⟩ := fit_peel (N' := 36) h rfl rfl
  obtain ⟨x_m3, h⟩ := fit_peel (N' := 37) h rfl rfl
  obtain ⟨x_facc, h⟩ := fit_peel (N' := 38) h rfl rfl
  obtain ⟨x_i1, h⟩ := fit_peel (N' := 39) h rfl rfl
  obtain ⟨x_b1, h⟩ := fit_peel (N' := 40) h rfl rfl
  obtain ⟨x_c1, h⟩ := fit_peel (N' := 41) h rfl rfl
  obtain ⟨x_dat, h⟩ := fit_peel (N' := 42) h rfl rfl
  obtain ⟨x_sz, h⟩ := fit_peel (N' := 43) h rfl rfl
  obtain ⟨x_pb, h⟩ := fit_peel (N' := 44) h rfl rfl
  obtain ⟨x_kb, h⟩ := fit_peel (N' := 45) h rfl rfl
  obtain ⟨x_chk, h⟩ := fit_peel (N' := 46) h rfl rfl
  obtain ⟨x_ct, h⟩ := fit_peel (N' := 47) h rfl rfl
  obtain ⟨x_ft, h⟩ := fit_peel (N' := 48) h rfl rfl
  obtain ⟨x_sb, h⟩ := fit_peel (N' := 49) h rfl rfl
  obtain ⟨x_gen, h⟩ := fit_peel (N' := 50) h rfl rfl
  obtain ⟨x_trB, h⟩ := fit_peel (N' := 51) h rfl rfl
  obtain ⟨x_gb, h⟩ := fit_peel (N' := 52) h rfl rfl
  obtain ⟨x_bb, h⟩ := fit_peel (N' := 53) h rfl rfl
  obtain ⟨x_sch, h⟩ := fit_peel (N' := 54) h rfl rfl
  obtain ⟨x_sb2, h⟩ := fit_peel (N' := 55) h rfl rfl
  obtain ⟨x_par, h⟩ := fit_peel (N' := 56) h rfl rfl
  obtain ⟨x_ib, h⟩ := fit_peel (N' := 57) h rfl rfl
  obtain ⟨x_it, h⟩ := fit_peel (N' := 58) h rfl rfl
  obtain ⟨x_st, h⟩ := fit_peel (N' := 59) h rfl rfl
  obtain ⟨x_b2, h⟩ := fit_peel (N' := 60) h rfl rfl
  obtain ⟨x_pc, h⟩ := fit_peel (N' := 61) h rfl rfl
  obtain ⟨x_rc, h⟩ := fit_peel (N' := 62) h rfl rfl
  obtain ⟨x_dg, h⟩ := fit_peel (N' := 63) h rfl rfl
  obtain ⟨x_dr, h⟩ := fit_peel (N' := 64) h rfl rfl
  obtain ⟨x_cand, h⟩ := fit_peel (N' := 65) h rfl rfl
  obtain ⟨x_et, h⟩ := fit_peel (N' := 66) h rfl rfl
  obtain ⟨x_br, h⟩ := fit_peel (N' := 67) h rfl rfl
  obtain ⟨x_cond, h⟩ := fit_peel (N' := 68) h rfl rfl
  obtain ⟨x_cd, h⟩ := fit_peel (N' := 69) h rfl rfl
  obtain ⟨x_gt, h⟩ := fit_peel (N' := 70) h rfl rfl
  obtain ⟨x_tw, h⟩ := fit_peel (N' := 71) h rfl rfl
  obtain ⟨x_pw, h⟩ := fit_peel (N' := 74) h rfl rfl
  obtain ⟨x_rb, h⟩ := fit_peel (N' := 77) h rfl rfl
  obtain ⟨x_mp, h⟩ := fit_peel (N' := 80) h rfl rfl
  obtain ⟨x_dc, h⟩ := fit_peel (N' := 83) h rfl rfl
  obtain ⟨x_bc, h⟩ := fit_peel (N' := 91) h rfl rfl
  obtain ⟨x_brel, h⟩ := fit_peel (N' := 112) h rfl rfl
  obtain ⟨x_brep, h⟩ := fit_peel (N' := 115) h rfl rfl
  obtain ⟨x_orb, h⟩ := fit_peel (N' := 147) h rfl rfl
  obtain ⟨x_fd, h⟩ := fit_peel (N' := 150) h rfl rfl
  obtain ⟨x_fs, h⟩ := fit_peel (N' := 153) h rfl rfl
  obtain ⟨x_cnt, h⟩ := fit_peel (N' := 158) h rfl rfl
  obtain ⟨x_pst, h⟩ := fit_peel (N' := 166) h rfl rfl
  obtain ⟨x_fac, h⟩ := fit_peel (N' := 169) h rfl rfl
  obtain ⟨x_mpsf, h⟩ := fit_peel (N' := 172) h rfl rfl
  obtain ⟨x_app, h⟩ := fit_peel (N' := 175) h rfl rfl
  obtain ⟨x_fs3, h⟩ := fit_peel (N' := 178) h rfl rfl
  obtain ⟨x_h, h⟩ := fit_peel (N' := 181) h rfl rfl
  obtain ⟨x_mb, h⟩ := fit_peel (N' := 184) h rfl rfl
  obtain ⟨x_ad, h⟩ := fit_peel (N' := 187) h rfl rfl
  obtain ⟨x_fh, h⟩ := fit_peel (N' := 190) h rfl rfl
  obtain ⟨x_fdd, h⟩ := fit_peel (N' := 193) h rfl rfl
  obtain ⟨x_frr, h⟩ := fit_peel (N' := 196) h rfl rfl
  obtain ⟨x_add, h⟩ := fit_peel (N' := 199) h rfl rfl
  obtain ⟨x_mpS, h⟩ := fit_peel (N' := 202) h rfl rfl
  obtain ⟨x_mpP, h⟩ := fit_peel (N' := 205) h rfl rfl
  obtain ⟨x_flt, h⟩ := fit_peel (N' := 208) h rfl rfl
  obtain ⟨x_inv, h⟩ := fit_peel (N' := 220) h rfl rfl
  obtain ⟨x_al, h⟩ := fit_peel (N' := 223) h rfl rfl
  obtain ⟨x_fnd, h⟩ := fit_peel (N' := 226) h rfl rfl
  obtain ⟨x_swt, h⟩ := fit_peel (N' := 229) h rfl rfl
  obtain ⟨x_mpT, h⟩ := fit_peel (N' := 232) h rfl rfl
  obtain ⟨x_mpG, h⟩ := fit_peel (N' := 235) h rfl rfl
  obtain ⟨x_bs, h⟩ := fit_peel (N' := 238) h rfl rfl
  obtain ⟨x_mpS2, h⟩ := fit_peel (N' := 241) h rfl rfl
  obtain ⟨x_cmp, h⟩ := fit_peel (N' := 245) h rfl rfl
  obtain ⟨x_mpI, h⟩ := fit_peel (N' := 248) h rfl rfl
  obtain ⟨x_fltI, h⟩ := fit_peel (N' := 251) h rfl rfl
  obtain ⟨x_fld, h⟩ := fit_peel (N' := 254) h rfl rfl
  obtain ⟨x_flt2, h⟩ := fit_peel (N' := 257) h rfl rfl
  obtain ⟨x_md, h⟩ := fit_peel (N' := 260) h rfl rfl
  obtain ⟨x_gth, h⟩ := fit_peel (N' := 264) h rfl rfl
  obtain ⟨x_fq, h⟩ := fit_peel (N' := 268) h rfl rfl
  obtain ⟨x_fnd2, h⟩ := fit_peel (N' := 271) h rfl rfl
  obtain ⟨x_flt3, h⟩ := fit_peel (N' := 274) h rfl rfl
  obtain ⟨x_mb2, h⟩ := fit_peel (N' := 277) h rfl rfl
  obtain ⟨x_mbe, h⟩ := fit_peel (N' := 280) h rfl rfl
  obtain ⟨x_mc, h⟩ := fit_peel (N' := 283) h rfl rfl
  obtain ⟨x_mcd, h⟩ := fit_peel (N' := 286) h rfl rfl
  obtain ⟨x_mg, h⟩ := fit_peel (N' := 289) h rfl rfl
  obtain ⟨x_al2, h⟩ := fit_peel (N' := 292) h rfl rfl
  obtain ⟨x_fe, h⟩ := fit_peel (N' := 295) h rfl rfl
  exact ⟨x_str.single,
    x_col.single,
    x_ts.single,
    x_tv.single,
    x_fr.single,
    x_cse.single,
    x_acp.single,
    x_pd.single,
    x_ps.single,
    x_g.single,
    x_grp.single,
    x_sf.single,
    x_sp.single,
    x_dom.single,
    x_s2b.single,
    x_s3.single,
    x_spp.single,
    x_des.single,
    x_ht.single,
    x_h2.single,
    x_spl.single,
    x_rf.single,
    x_df.single,
    x_vm.single,
    x_vf.single,
    x_cf.single,
    x_dv.single,
    x_dvv.single,
    x_run.single,
    x_di0.single,
    x_db.single,
    x_drun.single,
    x_dloop.single,
    x_mv.single,
    x_m0.single,
    x_m1.single,
    x_m3.single,
    x_facc.single,
    x_i1.single,
    x_b1.single,
    x_c1.single,
    x_dat.single,
    x_sz.single,
    x_pb.single,
    x_kb.single,
    x_chk.single,
    x_ct.single,
    x_ft.single,
    x_sb.single,
    x_gen.single,
    x_trB.single,
    x_gb.single,
    x_bb.single,
    x_sch.single,
    x_sb2.single,
    x_par.single,
    x_ib.single,
    x_it.single,
    x_st.single,
    x_b2.single,
    x_pc.single,
    x_rc.single,
    x_dg.single,
    x_dr.single,
    x_cand.single,
    x_et.single,
    x_br.single,
    x_cond.single,
    x_cd.single,
    x_gt.single,
    x_tw.single,
    x_pw,
    x_rb,
    x_mp,
    x_dc,
    x_bc,
    x_brel,
    x_brep,
    x_orb,
    x_fd,
    x_fs,
    x_cnt,
    x_pst,
    x_fac,
    x_mpsf,
    x_app,
    x_fs3,
    x_h,
    x_mb,
    x_ad,
    x_fh,
    x_fdd,
    x_frr,
    x_add,
    x_mpS,
    x_mpP,
    x_flt,
    x_inv,
    x_al,
    x_fnd,
    x_swt,
    x_mpT,
    x_mpG,
    x_bs,
    x_mpS2,
    x_cmp,
    x_mpI,
    x_fltI,
    x_fld,
    x_flt2,
    x_md,
    x_gth,
    x_fq,
    x_fnd2,
    x_flt3,
    x_mb2,
    x_mbe,
    x_mc,
    x_mcd,
    x_mg,
    x_al2,
    x_fe,
    h⟩


end GI.Impl
