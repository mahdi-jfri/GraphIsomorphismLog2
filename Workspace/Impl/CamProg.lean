import Workspace.Impl.CamPLoop
import Workspace.Impl.CamPFac
import Workspace.Impl.CamPAssemble
import Workspace.Impl.CamPMainMath
import Workspace.Impl.CamPOrder
import Workspace.Impl.CamPSearch

/-!
# The program `camProg` (layout and the main bodies)

The program, on input `encGroup gs` with `G = ⟨gs⟩`:
1. `o ← GroupOrder G`; if `o < n^(1+⌊log₂ n⌋)`, answer `[0]` (`camMainBody`).
2. Otherwise Maróti's theorem gives an identification `e` (`cam_normal_form`).
   `cs ← ChiefSeries G`; the socle is `N = ⟨cs[len − 2]⟩` (`camX_chief_last`).
3. The factor loop splits `N` into its `r` simple factors `T₀, …` (`camLoop_spec`).
4. `m` is read from `|T₀| = m!/2`, and `k` from the size `binom(m, k)` of an orbit of `T₀`.
5. If `m + 2 ≤ (k + 1)²`, answer `[2]`.
6. Otherwise, for each factor, restrict it to an orbit and call Johnson identification; the
   centralizer of the factor in `N` gives the column (`camFac_spec`).
7. Transpose the columns, and answer `[1, m, k, r, E]` (`cam_assemble`, `cam_out_one`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp len len_le_self)

/-- `n`, read from the input. -/
def camN : Expr := .get (.var 0) (.nat 0)

/-- The first factor. -/
def camT0 : Expr := .get (.get (.var 4) (.nat 1)) (.nat 0)

/-- Steps 2–7 (at `b + 1`). -/
def camTailBody (b jo jc : ℕ) : Expr :=
  .letE (.prim jc (.var 0)) <|
  .letE (.call (b + 2) (mk2 camN (.get (.var 1) (.arith .sub (.length (.var 1)) (.nat 2))))) <|
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

/-- All functions of the program, at base `b` (231 functions). -/
def camFuns (b jo jc jq jj : ℕ) : List Expr :=
  [camMainBody b jo] ++ [camTailBody b jo jc] ++ mkGroupFuns (b + 2) ++ camLoopFuns (b + 9) jo jc jq ++
    camRestrFuns (b + 20) ++ camMFuns (b + 83) ++ camKFuns (b + 88) ++ camSmallFuns (b + 93) ++
    mapFuns (b + 100) (b + 103) ++ camFacFuns (b + 103) jj jq ++ camTrFuns (b + 219)

/-- Where the parts of the program sit. -/
structure CamAt (P : Program) (b jo jc jq jj : ℕ) (ho : GroupOrder) (hc : ChiefSeriesAlgo)
    (hqc : QuotientCentralizer) (hj : JohnsonIdentification) : Prop where
  main : P.funs[b]? = some (camMainBody b jo)
  tail : P.funs[b + 1]? = some (camTailBody b jo jc)
  mg : P.HasAt (b + 2) (mkGroupFuns (b + 2))
  loop : CamLoopAt P (b + 9) jo jc jq ho hc hqc
  iter : P.HasAt (b + 17) (iterFuns (b + 17) (b + 9))
  restr : CamRestrAt P (b + 20)
  cm : P.HasAt (b + 83) (camMFuns (b + 83))
  ck : P.HasAt (b + 88) (camKFuns (b + 88))
  small : P.HasAt (b + 93) (camSmallFuns (b + 93))
  mp : P.HasAt (b + 100) (mapFuns (b + 100) (b + 103))
  fac : CamFacAt P (b + 103) jj jq hj hqc
  tr : P.HasAt (b + 219) (camTrFuns (b + 219))
  po : P.prims[jo]? = some (groupOrderPrim ho)
  pc : P.prims[jc]? = some (chiefSeriesPrim hc)

theorem camAt_of {P : Program} {b jo jc jq jj : ℕ} {ho : GroupOrder} {hc : ChiefSeriesAlgo}
    {hqc : QuotientCentralizer} {hj : JohnsonIdentification}
    (h : P.HasAt b (camFuns b jo jc jq jj))
    (po : P.prims[jo]? = some (groupOrderPrim ho)) (pc : P.prims[jc]? = some (chiefSeriesPrim hc))
    (pq : P.prims[jq]? = some (quotientCentralizerPrim hqc))
    (pj : P.prims[jj]? = some (johnsonPrim hj)) : CamAt P b jo jc jq jj ho hc hqc hj := by
  simp only [camFuns] at h
  have hL := camLoopAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.left.left.left.left.left.right) po pc pq
  exact
  { main := h.left.left.left.left.left.left.left.left.left.left.single
    tail := by simpa using h.left.left.left.left.left.left.left.left.left.right.single
    mg := by simpa [Nat.add_assoc] using h.left.left.left.left.left.left.left.left.right
    loop := hL.1
    iter := by simpa [Nat.add_assoc] using hL.2
    restr := camRestrAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.left.left.left.left.right)
    cm := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.left.left.left.right
    ck := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.left.left.right
    small := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.left.right
    mp := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.left.right
    fac := camFacAt_of (by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc] using h.left.right) pj pq
    tr := by simpa [mkGroupFuns, rangeFuns, appendFuns, loopFuns, camLoopFuns, iterFuns, length_camRestrFuns, camMFuns, camKFuns, advFuns, camSmallFuns, log2Funs, powFuns, mapFuns, Nat.add_assoc, camFacFuns, camColFuns, orbitFuns, gatherFuns, camIdxFuns, findEqFuns, length_orbitFuns] using h.right
    po := po
    pc := pc }

end GI.Impl
