module

public import Workspace.Impl.FinLayoutAgg
public import Workspace.Impl.AggCertOK

@[expose] public section

/-!
# The certificate phase in the final program

The slot of the certificate phase is fixed: its entry `crE` sits at `asb 2` and its
helper list `crF` at `fagCrIdx = asb 2000`, with room for `299000` functions (`FagFits`).
`asCertOK_of` proves `AsCertOK` for the function `cpCertE d f` from the place of the runner, the
loop, the move program and the program for `F_x`, `F_y`. Here we fill the slot.

**The helper list** `fcrFuns c` at base `c` (483 functions):

| offset | content | used as |
|---|---|---|
| `0` | `runBody asmF c (c + 1)` | the runner `d` |
| `1` | `cpLoopBody (c + 1) (c + 11)` | the loop `stp` |
| `2` | `cpFzFuns (c + 2) (c + 11)` (9 functions) | the program `f` for `F_x`, `F_y` |
| `11` | `cpMvFuns (c + 11) 0 2 1` (472 functions) | the move program `b` and its modules |

The move program calls **PointwiseStab** at primitive `0`, **Preimage** at `2` and
**Membership** at `1`, as in the primitive table. The final list is
`fcrF = fcrFuns fagCrIdx` and the entry is `fcrE = cpCertE fagCrIdx (fagCrIdx + 2)`.

`fag_asCertOK` is the contract `AsCertOK` in the final program, for every interface and the
bound `cpCertX`. It is the only result of this file used later (`CertReq.lean`), together with
the room `fcr_fits`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition DerivedSubgroup NormalizedIntersection
  NormalClosure)

/-! ### The move program from its function table -/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false


/-- Peel the last block of a left-nested list. -/
private theorem fcr_peel {P : Program} {b n : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (hn : A.length = n) : P.HasAt b A ∧ P.HasAt (b + n) B := ⟨h.left, hn ▸ h.right⟩

local macro "fcr_blk_len" : tactic => `(tactic| (
  dsimp only [incFuns, graphStabFuns, ptFuns, tailFuns, mkGroupFuns,
    ckFindFuns, graphTupFuns, pSplitMapFuns, krFuns, wpFuns, ansGensFuns, closFuns,
    tupOrbFuns, pSplitFuns, clSwapFuns, invFuns, findEqFuns, cpFzFuns]
  simp only [List.length_append, length_domFuns, length_imgCardFuns, length_orbTFuns,
    length_orbitFuns, length_pEncMapFuns, length_filterFuns, length_rangeFuns]
  rfl))

private theorem l_inc (b j : ℕ) : (incFuns b j).length = 132 := by fcr_blk_len
private theorem l_stab (b j : ℕ) : (graphStabFuns b j).length = 33 := by fcr_blk_len
private theorem l_pt (b j : ℕ) : (ptFuns b j).length = 63 := by fcr_blk_len
private theorem l_tail (b : ℕ) : (tailFuns b).length = 3 := rfl
private theorem l_mkG (b : ℕ) : (mkGroupFuns b).length = 7 := by fcr_blk_len
private theorem l_find (b j : ℕ) : (ckFindFuns b j).length = 9 := by fcr_blk_len
private theorem l_tup (b : ℕ) : (graphTupFuns b).length = 37 := by fcr_blk_len
private theorem l_map (b f : ℕ) : (mapFuns b f).length = 3 := rfl
private theorem l_split (b : ℕ) : (pSplitMapFuns b).length = 12 := by fcr_blk_len
private theorem l_app (b : ℕ) : (appendFuns b).length = 3 := rfl
private theorem l_kr (b j : ℕ) : (krFuns b j).length = 20 := by fcr_blk_len
private theorem l_cnt (b : ℕ) : (countFuns b).length = 5 := rfl
private theorem l_wp (b d : ℕ) : (wpFuns b d).length = 15 := by fcr_blk_len
private theorem l_ansG (b : ℕ) : (ansGensFuns b).length = 8 := by fcr_blk_len
private theorem l_clos (b j : ℕ) : (closFuns b j).length = 55 := by fcr_blk_len
private theorem l_fz (b f : ℕ) : (cpFzFuns b f).length = 9 := by fcr_blk_len

macro "fcr_len" : tactic => `(tactic| (
  try dsimp only [cpMvFuns]
  try simp only [List.length_append, length_domFuns, length_pEncMapFuns, length_filterFuns,
    length_rangeFuns, l_inc, l_stab, l_pt, l_tail, l_mkG, l_find, l_tup, l_map, l_split,
    l_app, l_kr, l_cnt, l_wp, l_ansG, l_clos, l_fz]
  rfl))

/-- **The place of the move program** from the position of its function table. -/
theorem fcrMvAt_of {P : Program} {b jp jpre jm : ℕ} (h : P.HasAt b (cpMvFuns b jp jpre jm)) :
    CpMvAt P b jp jpre jm := by
  unfold cpMvFuns at h
  obtain ⟨h, h_filt⟩ := fcr_peel h (n := 469) (by fcr_len)
  obtain ⟨h, h_clos⟩ := fcr_peel h (n := 414) (by fcr_len)
  obtain ⟨h, h_ansG⟩ := fcr_peel h (n := 406) (by fcr_len)
  obtain ⟨h, h_dom⟩ := fcr_peel h (n := 381) (by fcr_len)
  obtain ⟨h, h_wp⟩ := fcr_peel h (n := 366) (by fcr_len)
  obtain ⟨h, h_cnt⟩ := fcr_peel h (n := 361) (by fcr_len)
  obtain ⟨h, h_mapInd⟩ := fcr_peel h (n := 358) (by fcr_len)
  obtain ⟨h, h_range⟩ := fcr_peel h (n := 355) (by fcr_len)
  obtain ⟨h, h_kr⟩ := fcr_peel h (n := 335) (by fcr_len)
  obtain ⟨h, h_app⟩ := fcr_peel h (n := 332) (by fcr_len)
  obtain ⟨h, h_fstF⟩ := fcr_peel h (n := 331) (by fcr_len)
  obtain ⟨h, h_mapFst⟩ := fcr_peel h (n := 328) (by fcr_len)
  obtain ⟨h, h_split⟩ := fcr_peel h (n := 316) (by fcr_len)
  obtain ⟨h, h_mapSec⟩ := fcr_peel h (n := 313) (by fcr_len)
  obtain ⟨h, h_tup⟩ := fcr_peel h (n := 276) (by fcr_len)
  obtain ⟨h, h_find⟩ := fcr_peel h (n := 267) (by fcr_len)
  obtain ⟨h, h_mkG⟩ := fcr_peel h (n := 260) (by fcr_len)
  obtain ⟨h, h_pEnc⟩ := fcr_peel h (n := 247) (by fcr_len)
  obtain ⟨h, h_tail⟩ := fcr_peel h (n := 244) (by fcr_len)
  obtain ⟨h, h_pt⟩ := fcr_peel h (n := 181) (by fcr_len)
  obtain ⟨h, h_stab⟩ := fcr_peel h (n := 148) (by fcr_len)
  obtain ⟨h, h_inc⟩ := fcr_peel h (n := 16) (by fcr_len)
  have hs := h
  exact {
    mv := by simpa using (hs.block 0 (gs := [cpMvF b]) (by rfl)).single
    round := (hs.block 1 (gs := [cpRoundF b]) (by rfl)).single
    fin := (hs.block 2 (gs := [cpEndF b]) (by rfl)).single
    start := (hs.block 3 (gs := [cpStartF b]) (by rfl)).single
    reps := (hs.block 4 (gs := [cpRepsF b]) (by rfl)).single
    win := (hs.block 5 (gs := [cpWinF b]) (by rfl)).single
    sec := (hs.block 6 (gs := [cpSecF]) (by rfl)).single
    indStep := (hs.block 7 (gs := [cpIndStepF b]) (by rfl)).single
    diffTest := (hs.block 8 (gs := [cpDiffTestF b]) (by rfl)).single
    next := (hs.block 9 (gs := [cpNextF b]) (by rfl)).single
    close := (hs.block 10 (gs := [cpCloseF b]) (by rfl)).single
    ind := (hs.block 11 (gs := [cpIndF b]) (by rfl)).single
    inc := h_inc
    stab := h_stab
    pt := h_pt
    tail := h_tail
    pEnc := h_pEnc
    mkG := h_mkG
    find := h_find
    tup := h_tup
    mapSec := h_mapSec
    split := h_split
    mapFst := h_mapFst
    fstF := h_fstF.single
    app := h_app
    kr := h_kr
    range := h_range
    mapInd := h_mapInd
    cnt := h_cnt
    wp := h_wp
    dom := domAt_of_hasAt h_dom
    ansG := h_ansG
    clos := h_clos
    filt := h_filt
  }

theorem length_cpMvFuns (b jp jpre jm : ℕ) : (cpMvFuns b jp jpre jm).length = 472 := by fcr_len

/-! ### The helper list -/

/-- **The helper list of the certificate phase** at base `c`: the runner, the loop, the program
for `F_x`, `F_y` and the move program (see the module docstring). -/
def fcrFuns (c : ℕ) : List Expr :=
  [runBody asmF c (c + 1), cpLoopBody (c + 1) (c + 11)] ++ cpFzFuns (c + 2) (c + 11) ++
    cpMvFuns (c + 11) 0 2 1

theorem length_fcrFuns (c : ℕ) : (fcrFuns c).length = 483 := by
  unfold fcrFuns; fcr_len

/-- The entry of the certificate phase for the helper list at base `c`. -/
def fcrEntry (c : ℕ) : Expr := cpCertE c (c + 2)

/-- **The helper list in the final program**, at `fagCrIdx`. -/
def fcrF : List Expr := fcrFuns fagCrIdx

/-- **The entry in the final program**, at `asb 2`. -/
def fcrE : Expr := fcrEntry fagCrIdx

/-- The helper list fits its room of `299000` functions. -/
theorem fcr_fits : fcrF.length ≤ fagCmOff - fagCrOff := by
  rw [fcrF, length_fcrFuns]; unfold fagCmOff fagCrOff; omega

/-- **The parts of the helper list** at their indices, from its position at base `c`. -/
theorem fcr_parts {P : Program} {c : ℕ} (h : P.HasAt c (fcrFuns c)) :
    P.funs[c]? = some (runBody asmF c (c + 1)) ∧
      P.funs[c + 1]? = some (cpLoopBody (c + 1) (c + 11)) ∧
      CpFzAt P (c + 2) (c + 11) ∧ CpMvAt P (c + 11) 0 2 1 := by
  have h0 := h.left.left
  have hfz : P.HasAt (c + 2) (cpFzFuns (c + 2) (c + 11)) := h.left.right
  have hmv : P.HasAt (c + 11) (cpMvFuns (c + 11) 0 2 1) := h.right
  exact ⟨(h0.block 0 (gs := [runBody asmF c (c + 1)]) (by rfl)).single,
    (h0.block 1 (gs := [cpLoopBody (c + 1) (c + 11)]) (by rfl)).single, cpFzAt_of _ _ hfz,
    fcrMvAt_of hmv⟩

/-! ### The contract in the final program -/

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
  {hder : DerivedSubgroup} {hni : NormalizedIntersection}
  {hnc : NormalClosure}
  {ext : List Prim} {recF labF jF : List Expr}

/-- PointwiseStab is primitive `0` of the final program. -/
theorem fcr_prim_pst {cmE itE : Expr} {cmF itF : List Expr} :
    (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF fcrE cmE
      itE fcrF cmF itF).prims[0]? = some (pointwiseStabPrim hst) := rfl

/-- Membership is primitive `1` of the final program. -/
theorem fcr_prim_mem {cmE itE : Expr} {cmF itF : List Expr} :
    (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF fcrE cmE
      itE fcrF cmF itF).prims[1]? = some (membershipPrim hm) := rfl

/-- **The certificate phase in the final program.** For every interface `I`, the entry `fcrE`
at `asb 2` with the helper list `fcrF` at `fagCrIdx` satisfies `AsCertOK` for the hand-over
`asHandImpl` and the bound `cpCertX`. The cited results enter through the three primitives at
`0`, `2`, `1`. -/
theorem fag_asCertOK (I : Iface) (hF : FlcFits recF labF jF) {cmE itE : Expr}
    {cmF itF : List Expr} (hcm : cmF.length ≤ fagItOff - fagCmOff) :
    AsCertOK I (fagProg hst hm hpre hfac hmb hO hC hder hni hnc ext recF labF jF
      fcrE cmE itE fcrF cmF itF) asmF asHandImpl (cpCertX hst hpre hm) (asb 2) := by
  obtain ⟨-, h2, -, -, -, hcr, -⟩ := fag_hasAt (hst := hst) (hm := hm) (hpre := hpre)
    (hfac := hfac) (hmb := hmb) (hO := hO) (hC := hC) (hder := hder)
    (hni := hni) (hnc := hnc) (ext := ext) hF (crE := fcrE)
    (cmE := cmE) (itE := itE) (itF := itF) ⟨fcr_fits, hcm⟩
  obtain ⟨hd, hstp, hfz, hmv⟩ := fcr_parts hcr
  exact asCertOK_of hst hpre hm I _ asmF asHandImpl _ h2 hd hstp hmv hfz fcr_prim_pst
    fag_prim_pre fcr_prim_mem (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h) (fun _ => le_rfl)

end Asm

end GI.Impl
