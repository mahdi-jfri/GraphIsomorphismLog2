import Workspace.Impl.FinLayoutCert
import Workspace.Impl.AggCmpRun
import Workspace.Impl.FinLayoutItemsHand

/-!
# The comparison phase in the final program

The slot of the comparison phase is fixed: its entry `cmE` sits at `asb 3` and its
helper list `cmF` at `fagCmIdx = asb 301000`, with room for `300000` functions (`FagFits`).
`cm_asCompOK` proves `AsCompOK` for the setup function `cmSetF b d tb` from its layout `CmSetAt`;
`fitm_cmAsCompOKB` (`FinLayoutItemsHand.lean`) is the same result for the
hand-over `ItHandB` of the items. Here we fill the slot.

**The helper list** `fcmFuns c` at base `c` (665 functions):

| offset | content | used as |
|---|---|---|
| `0` | `runBody asmF c (c + 1)` | the runner `d` |
| `1` | `cpLoopBody (c + 1) (c + 100)` | the loop `stp` |
| `10` | `cmTFuns (c + 10)` (22 functions) | the test tuples `tb` |
| `100` | `fcmMvFuns (c + 100) 1 0` (565 functions) | the move program `b` and its modules |

Inside `fcmMvFuns b jm jp` the functions sit at the offsets that `CmMvAt0`, `CmStAt` and
`CmClAt` fix: the fourteen single functions at `b … b + 13`, then the modules at `cmComp b =
b + 16`, `cmFind b = b + 20`, `b + 100 … b + 240` (start of a pair) and `b + 500 … b + 540`
(call of a stage); the gaps are padded with `.nil`.

The comparison program calls **Membership** at primitive `1` and **PointwiseStab** at `0`, as in
the primitive table. The final list is `fcmF = fcmFuns fagCmIdx` and the entry is
`fcmE = cmSetF (fagCmIdx + 100) fagCmIdx (fagCmIdx + 10)`.

`fag_asCompOK` is the contract `AsCompOK` in the final program, for every interface and the bound
`cmRunX`. It and the room `fcm_fits` are the results used later (`CmpReq.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition ChiefSeriesAlgo DerivedSubgroup QuotientCentralizer NormalizedIntersection
  SylowAlgo SylowConjugate NormalClosure)

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ### The move program and its modules -/

/-- **The functions of the comparison program** at base `b` (see the module docstring). -/
def fcmMvFuns (b jm jp : ℕ) : List Expr :=
  asmPad 16 ([cmMvF b, cmPairF b, cmStageF b, cmAnsF b, cmCallF b, cmStartF b, sbAddF, orbTestF (cmEqN b), cmChF b, cmLTstF b, cmIndStepF (cmCnt b), cmIndF (cmRng b) (cmIMap b), cmLogF b, cmKerF b]) ++
    (asmPad 4 (composeFuns (cmComp b)) ++
    (asmPad 80 (cmFindFuns (cmFind b) jm) ++
    (asmPad 3 (mapFuns (cmShM b) (b + 6)) ++
    (asmPad 3 (eqNatsFuns (cmEqN b)) ++
    (asmPad 3 (findFuns (cmKFd b) (b + 7)) ++
    (asmPad 3 (rangeFuns (cmRng b)) ++
    (asmPad 8 (gatherFuns (cmGat b)) ++
    (asmPad 80 (graphStabFuns (cmStab b) jp) ++
    (asmPad 40 (graphTupFuns (cmTup b)) ++
    (asmPad 260 (krFuns (cmKr b) jp) ++
    (asmPad 3 (findFuns (cmLFd b) (b + 9)) ++
    (asmPad 7 (mapFuns (cmIMap b) (b + 10)) ++
    (asmPad 10 (countFuns (cmCnt b)) ++
    (asmPad 20 (cmWpFuns (cmWpB b) (cmDomB b)) ++
    (domFuns (cmDomB b))))))))))))))))

/-- Split off a padded block. -/
private theorem fcm_peel {P : Program} {b n : ℕ} {A B : List Expr}
    (h : P.HasAt b (asmPad n A ++ B)) (hA : A.length ≤ n) : P.HasAt b A ∧ P.HasAt (b + n) B :=
  ⟨h.left.left, by simpa [length_asmPad hA] using h.right⟩

macro "fcm_len" : tactic => `(tactic| simp only [List.length_append, List.length_cons,
  List.length_nil, allFuns, appendFuns, cmFindFuns, cmTFuns, cmWpFuns, composeFuns, countFuns, domFuns, eqNatsFuns, filterFuns, findEqFuns, findFuns, foldlFuns, gatherFuns, graphStabFuns, graphTupFuns, invFuns, krFuns, leFuns, loopFuns, mapFuns, mkGroupFuns, orbTFuns, pEncMapFuns, pSplitFuns, pSplitMapFuns, rangeFuns, redFuns, rightMapFuns, stDDecFuns, stDPowFuns, tupOrbFuns, wrMapFuns] <;> omega)

theorem length_fcmMvFuns (b jm jp : ℕ) : (fcmMvFuns b jm jp).length = 565 := by
  simp only [fcmMvFuns, asmPad, List.length_append, List.length_replicate]
  fcm_len

set_option maxHeartbeats 1000000 in
/-- **The layout of the comparison modules** from the position of `fcmMvFuns`. -/
theorem fcm_mv_parts {P : Program} {b jm jp : ℕ} (h : P.HasAt b (fcmMvFuns b jm jp)) :
    CmMvAt0 P b jm ∧ CmStAt P b jp ∧ CmClAt P b := by
  unfold fcmMvFuns at h
  obtain ⟨h_S, h0⟩ := fcm_peel h (by fcm_len)
  obtain ⟨h_comp, h1⟩ := fcm_peel h0 (by fcm_len)
  obtain ⟨h_find, h2⟩ := fcm_peel h1 (by fcm_len)
  obtain ⟨h_shM, h3⟩ := fcm_peel h2 (by fcm_len)
  obtain ⟨h_eqN, h4⟩ := fcm_peel h3 (by fcm_len)
  obtain ⟨h_kfd, h5⟩ := fcm_peel h4 (by fcm_len)
  obtain ⟨h_rng, h6⟩ := fcm_peel h5 (by fcm_len)
  obtain ⟨h_gat, h7⟩ := fcm_peel h6 (by fcm_len)
  obtain ⟨h_stab, h8⟩ := fcm_peel h7 (by fcm_len)
  obtain ⟨h_tup, h9⟩ := fcm_peel h8 (by fcm_len)
  obtain ⟨h_kr, h10⟩ := fcm_peel h9 (by fcm_len)
  obtain ⟨h_lfd, h11⟩ := fcm_peel h10 (by fcm_len)
  obtain ⟨h_imap, h12⟩ := fcm_peel h11 (by fcm_len)
  obtain ⟨h_cnt, h13⟩ := fcm_peel h12 (by fcm_len)
  obtain ⟨h_wp, h14⟩ := fcm_peel h13 (by fcm_len)
  have h_dom := h14
  refine ⟨⟨(h_S.block 0 (gs := [cmMvF b]) (by rfl)).single, (h_S.block 1 (gs := [cmPairF b]) (by rfl)).single, (h_S.block 2 (gs := [cmStageF b]) (by rfl)).single, (h_S.block 3 (gs := [cmAnsF b]) (by rfl)).single, h_comp, h_find⟩, ?_, ?_⟩
  · exact ⟨(h_S.block 5 (gs := [cmStartF b]) (by rfl)).single, (h_S.block 6 (gs := [sbAddF]) (by rfl)).single, (h_S.block 7 (gs := [orbTestF (cmEqN b)]) (by rfl)).single, (h_S.block 8 (gs := [cmChF b]) (by rfl)).single,
      h_shM, h_eqN, h_kfd, h_rng, h_gat, h_stab, h_tup, h_kr⟩
  · exact ⟨(h_S.block 4 (gs := [cmCallF b]) (by rfl)).single, (h_S.block 9 (gs := [cmLTstF b]) (by rfl)).single, (h_S.block 10 (gs := [cmIndStepF (cmCnt b)]) (by rfl)).single, (h_S.block 11 (gs := [cmIndF (cmRng b) (cmIMap b)]) (by rfl)).single, (h_S.block 12 (gs := [cmLogF b]) (by rfl)).single, (h_S.block 13 (gs := [cmKerF b]) (by rfl)).single,
      h_lfd, h_imap, h_cnt, h_wp, domAt_of_hasAt h_dom⟩

/-! ### The helper list -/

/-- **The helper list of the comparison phase** at base `c`: the runner, the loop, the test
tuples and the move program (see the module docstring). -/
def fcmFuns (c : ℕ) : List Expr :=
  asmPad 10 [runBody asmF c (c + 1), cpLoopBody (c + 1) (c + 100)] ++
    (asmPad 90 (cmTFuns (c + 10)) ++ fcmMvFuns (c + 100) 1 0)

theorem length_fcmFuns (c : ℕ) : (fcmFuns c).length = 665 := by
  unfold fcmFuns
  simp only [asmPad, List.length_append, List.length_replicate, length_fcmMvFuns]
  fcm_len

/-- The setup function for the helper list at base `c`. -/
noncomputable def fcmEntry (c : ℕ) : Expr := cmSetF (c + 100) c (c + 10)

/-- **The helper list in the final program**, at `fagCmIdx`. -/
def fcmF : List Expr := fcmFuns fagCmIdx

/-- **The entry in the final program**, at `asb 3`. -/
noncomputable def fcmE : Expr := fcmEntry fagCmIdx

/-- The helper list fits its room of `300000` functions. -/
theorem fcm_fits : fcmF.length ≤ fagItOff - fagCmOff := by
  rw [fcmF, length_fcmFuns]; unfold fagItOff fagCmOff; omega

/-- **The layout `CmSetAt`** from the entry at `fm` and the helper list at base `c`. -/
theorem fcm_setAt {P : Program} {F : Funs} {hst : PointwiseStab} {hm : Membership} {fm c : ℕ}
    (hF : F = asmF) (he : P.funs[fm]? = some (fcmEntry c)) (h : P.HasAt c (fcmFuns c))
    (hjm : P.prims[1]? = some (membershipPrim hm))
    (hjp : P.prims[0]? = some (pointwiseStabPrim hst)) :
    CmSetAt P F hst hm fm (c + 100) c (c + 1) (c + 10) 1 0 := by
  subst hF
  unfold fcmFuns at h
  obtain ⟨h0, h1⟩ := fcm_peel h (by simp)
  obtain ⟨ht, hmv⟩ := fcm_peel h1 (by fcm_len)
  obtain ⟨hmv0, hst', hcl⟩ := fcm_mv_parts hmv
  exact ⟨he, ht, (h0.block 0 (gs := [runBody asmF c (c + 1)]) (by rfl)).single,
    (h0.block 1 (gs := [cpLoopBody (c + 1) (c + 100)]) (by rfl)).single, hmv0, hst', hcl, hjm, hjp⟩

/-! ### The contract in the final program -/

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition} {hcs : ChiefSeriesAlgo}
  {hder : DerivedSubgroup} {hqc : QuotientCentralizer} {hni : NormalizedIntersection}
  {hsy : SylowAlgo} {hsc : SylowConjugate} {hnc : NormalClosure}
  {ext : List Prim} {recF labF jF : List Expr}

/-- **The comparison phase in the final program.** For every interface `I`, the entry `fcmE` at
`asb 3` with the helper list `fcmF` at `fagCmIdx` satisfies `AsCompOK` for the hand-over
`asHandImpl` and the bound `cmRunX`. The cited results enter through the primitives at `1`
and `0`. -/
theorem fag_asCompOK (I : Iface) (hF : FlcFits recF labF jF) {crE itE : Expr}
    {crF itF : List Expr} (hcr : crF.length ≤ fagCmOff - fagCrOff) :
    AsCompOK I (fagProg hst hm hpre hfac hmb hO hC hcs hder hqc hni hsy hsc hnc ext recF labF jF
      crE fcmE itE crF fcmF itF) asmF asHandImpl (cmRunX hst hpre hm) (asb 3) := by
  obtain ⟨-, -, h3, -, -, -, hcm, -⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hcs := hcs) (hder := hder) (hqc := hqc)
    (hni := hni) (hsy := hsy) (hsc := hsc) (hnc := hnc) (ext := ext) hF (crE := crE)
    (cmE := fcmE) (itE := itE) (itF := itF) ⟨hcr, fcm_fits⟩
  -- `fitm_cmAsCompOKB`: the hand-over of the items is `ItHandB` (`asHandImpl`)
  exact fitm_cmAsCompOKB I _ asmF hst hpre hm asHandImpl (fcm_setAt rfl h3 hcm rfl rfl)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

end Asm

end GI.Impl
