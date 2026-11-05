module

public import Workspace.Impl.CamPLoop
public import Workspace.Impl.CamPFac
public import Workspace.Impl.CamPAssemble
public import Workspace.Impl.CamPMainMath
public import Workspace.Impl.CamPOrder
public import Workspace.Impl.CamPSearch

@[expose] public section

/-!
# The program `camProg` (layout and the main bodies)

The program, on input `encGroup gs` with `G = ⟨gs⟩`:
1. `o ← GroupOrder G`; if `o < n^(1+⌊log₂ n⌋)`, answer `[0]` (`camMainBody`).
2. Otherwise Maróti's theorem gives an identification `e` (`cam_normal_form`).
   `camSocleFuns` finds the socle `N = camProd e univ` (`camSocle_spec`).
3. The factor loop splits `N` into its `r` simple factors `T₀, …` (`camLoop_spec`).
4. `m` is read from `|T₀| = m!/2`, and `k` from the size `binom(m, k)` of an orbit of `T₀`.
5. If `m + 2 ≤ (k + 1)²`, answer `[2]`.
6. Otherwise, for each factor, restrict it to an orbit and call Johnson identification; the
   centralizer of the factor in `N` gives the column (`camFac_spec`).
7. Transpose the columns, and answer `[1, m, k, r, E]` (`cam_assemble`, `cam_out_one`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp len len_le_self)

/-- `n`, read from the input. -/
def camN : Expr := .get (.var 0) (.nat 0)

/-- The first factor. -/
def camT0 : Expr := .get (.get (.var 4) (.nat 1)) (.nat 0)

/-- Steps 2–7 (at `b + 1`). -/
def camTailBody (b jo : ℕ) : Expr :=
  .letE (.call (b + 231) (.var 0)) <|
  .letE (.call (b + 2) (mk2 camN (.var 1))) <|
  .letE (.call (b + 2) (mk2 camN .nil)) <|
  .letE (.call (b + 17) (mk3 (.var 3) camN (mk2 (.var 2) .nil))) <|
  .letE (.prim jo camT0) <|
  .letE (.call (b + 83) (mk2 (.var 5) camN)) <|
  .letE (.call (b + 20) (mk2 .nil camT0)) <|
  .letE (.call (b + 88) (mk2 (.var 6) (.length (.get (.var 7) (.nat 0))))) <|
  .ite (.arith .lt (.arith .add (.var 6) (.nat 1))
      (.arith .mul (.arith .add (.var 8) (.nat 1)) (.arith .add (.var 8) (.nat 1))))
    (.snoc .nil (.nat 2)) <|
  .letE (.call (b + 100) (mk2 (mk4 (.var 2) (.var 3) (.var 6) (.var 8)) (.get (.var 4) (.nat 1)))) <|
  .letE (.call (b + 219) (mk2 camN (.var 9))) <|
  .snoc (mk4 (.nat 1) (.var 6) (.var 8) (.length (.get (.var 4) (.nat 1)))) (.var 10)

/-- Step 1 (at `b`). -/
def camMainBody (b jo : ℕ) : Expr :=
  .letE (.prim jo (.var 0))
    (.ite (.call (b + 93) (mk2 (.var 1) camN)) (.snoc .nil (.nat 0)) (.call (b + 1) (.var 0)))

/-- All functions of the program, at base `b` (343 functions). -/
def camFuns (b jo jp jn jd jq jj : ℕ) : List Expr :=
  [camMainBody b jo] ++ [camTailBody b jo] ++ mkGroupFuns (b + 2) ++
    camLoopFuns (b + 9) (b + 289) jo jq ++
    camRestrFuns (b + 20) ++ camMFuns (b + 83) ++ camKFuns (b + 88) ++ camSmallFuns (b + 93) ++
    mapFuns (b + 100) (b + 103) ++ camFacFuns (b + 103) jj jq ++ camTrFuns (b + 219) ++
    camSocleFuns (b + 231) jo jp jn jd ++ camFactorFuns (b + 289) jo jp jn

/-- Where the parts of the program sit. -/
structure CamAt (P : Program) (b jo jp jn jd jq jj : ℕ) (ho : GroupOrder)
    (hp : PointwiseStab) (hncl : NormalClosure) (hd : DerivedSubgroup)
    (hqc : GMPNormalCentralizer) (hj : JohnsonIdentification) : Prop where
  main : P.funs[b]? = some (camMainBody b jo)
  tail : P.funs[b + 1]? = some (camTailBody b jo)
  mg : P.HasAt (b + 2) (mkGroupFuns (b + 2))
  loop : CamLoopAt P (b + 9) (b + 289) jo jp jn jq ho hp hncl hqc
  iter : P.HasAt (b + 17) (iterFuns (b + 17) (b + 9))
  restr : CamRestrAt P (b + 20)
  cm : P.HasAt (b + 83) (camMFuns (b + 83))
  ck : P.HasAt (b + 88) (camKFuns (b + 88))
  small : P.HasAt (b + 93) (camSmallFuns (b + 93))
  mp : P.HasAt (b + 100) (mapFuns (b + 100) (b + 103))
  fac : CamFacAt P (b + 103) jj jq hj hqc
  tr : P.HasAt (b + 219) (camTrFuns (b + 219))
  soc : CamSocleAt P (b + 231) jo jp jn jd ho hp hncl hd
  po : P.prims[jo]? = some (groupOrderPrim ho)

theorem camAt_of {P : Program} {b jo jp jn jd jq jj : ℕ} {ho : GroupOrder}
    {hp : PointwiseStab} {hncl : NormalClosure} {hd : DerivedSubgroup}
    {hqc : GMPNormalCentralizer} {hj : JohnsonIdentification}
    (h : P.HasAt b (camFuns b jo jp jn jd jq jj))
    (po : P.prims[jo]? = some (groupOrderPrim ho))
    (pp : P.prims[jp]? = some (pointwiseStabPrim hp))
    (pn : P.prims[jn]? = some (normalClosurePrim hncl))
    (pd : P.prims[jd]? = some (derivedSubgroupPrim hd))
    (pq : P.prims[jq]? = some (gmpNormalCentralizerPrim hqc))
    (pj : P.prims[jj]? = some (johnsonPrim hj)) :
    CamAt P b jo jp jn jd jq jj ho hp hncl hd hqc hj := by
  simp only [camFuns] at h
  have h0 := h.left.left
  have hdfac := camFactorAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc, camFacFuns, camColFuns, gatherFuns, camIdxFuns, findEqFuns, findFuns, length_orbitFuns, camTrFuns, length_camSocleFuns] using h.right) po pp pn
  have hsoc := camSocleAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc, camFacFuns, camColFuns, gatherFuns, camIdxFuns, findEqFuns, findFuns, length_orbitFuns, camTrFuns] using h.left.right) po pp pn pd
  have hL := camLoopAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.left.left.left.left.left.right) hdfac po pq
  exact
  { main := h0.left.left.left.left.left.left.left.left.left.left.single
    tail := by simpa using h0.left.left.left.left.left.left.left.left.left.right.single
    mg := by simpa [Nat.add_assoc] using h0.left.left.left.left.left.left.left.left.right
    loop := hL.1
    iter := by simpa [Nat.add_assoc] using hL.2
    restr := camRestrAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.left.left.left.left.right)
    cm := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.left.left.left.right
    ck := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.left.left.right
    small := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.left.right
    mp := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.left.right
    fac := camFacAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h0.left.right) pj pq
    tr := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc, camFacFuns, camColFuns, gatherFuns, camIdxFuns, findEqFuns, findFuns, length_orbitFuns] using h0.right
    soc := hsoc
    po := po }

end GI.Impl
