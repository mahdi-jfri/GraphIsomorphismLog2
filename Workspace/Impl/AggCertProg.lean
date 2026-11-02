import Workspace.Impl.AggCertBud

/-!
# The move program of the certificate phase

This file writes the move function `mv` of the loop `cpLoopBody` (`AggCertLoop.lean`) as a
`GI.Lang` program. Its argument is a program state `[kst, u]` (layout in `AggCertRep.lean`).

The parent data `par` (entry 0 of `kst`) is
`[sv, [k, q], ⟨graph of G⟩, n, D, ⟨domain points⟩, pSplitCtx k q, k + q]`, where `sv` is the
parent's canonical state value, `n = |dom|` and `D = |Alt(T)|` (the same for every test set).

The functions, at base `b`:

* `b`: dispatch on whether the program is inside a round (`inner ≠ []`);
* `b + 1`: start of a round: at `t = n` the end of a string (`b + 2`); else the increment
  (`inc_spec`), and if it is empty the next round, else the first window call (`b + 3`);
* `b + 2`: end of a string: start `y`, or start the next test set (`ptGraph_spec`, `tail`), or
  return the results;
* `b + 3`: first window call of a round: kernel (`graphStabP_spec`), cache key, lookup
  (`ckFind_spec`), representatives (`b + 4`), window group (`kr_spec`), window indicator
  (`b + 11`), window colors (`wp_spec`);
* `b + 4`: representatives: the cached ones, or the transversal of the tuple orbit
  (`graphTup_spec`, `pSplitMap_spec`) recorded in a new cache entry;
* `b + 5`: inside a round: the generators of the answer (`ansGens_spec`, `append`), then the
  next window call (`b + 9`) or the end of the round (`b + 10`: `clos_spec`, list difference);
* `b + 6`, `b + 7`, `b + 8`: steps of maps and filters; `b + 11`: the window indicator.

Every move that ends a round (an empty increment in `b + 1`, or `b + 10`) adds the stage
`[ps, increment]` to the log `lz` (entry 12). The end of `x` moves `lz` to `lx` (entry 13); the
end of `y` adds `[T, lx, lz]` to `logs` (entry 14), and the final output is `[⟨res⟩, ⟨logs⟩]`.
The other moves copy these three entries.

The library modules sit from `b + 16` on (`CpMvAt`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-! ### Reading the program state -/

/-- `kst`, entry 0 of the argument. -/
def cpKs : Expr := .get (.var 0) (.nat 0)

/-- Entry `j` of `kst`. -/
def cpKf (j : ℕ) : Expr := .get cpKs (.nat j)

/-- Entry `j` of `par`. -/
def cpPf (j : ℕ) : Expr := .get (cpKf 0) (.nat j)

/-- Entry `j` of the parent's state value. -/
def cpSf (j : ℕ) : Expr := .get (cpPf 0) (.nat j)

/-- Entry `j` of `inner`. -/
def cpIf (j : ℕ) : Expr := .get (cpKf 10) (.nat j)

/-- The codes of the current string: `yv` for `s = 1`, `xv` for `s = 0`. -/
def cpZv : Expr := .ite (cpKf 2) (cpSf 4) (cpSf 3)

/-- The window value of a call, from the group value `gv`, the indicator `dv` and the colors
`cv = [X, Y]`. -/
def cpWinE (gv dv cv : Expr) : Expr :=
  Expr.mkList [cpSf 0, gv, dv, .get cv (.nat 0), .get cv (.nat 1), cpSf 5, .nil, .nat 0, .nat 2,
    cpSf 9]

/-! ### The functions -/

section Funs

variable (b : ℕ)

/-- Base indices of the library modules. -/
def cpInc : ℕ := b + 16
def cpStab : ℕ := b + 148
def cpPt : ℕ := b + 181
def cpTail : ℕ := b + 244
def cpPEnc : ℕ := b + 247
def cpMkG : ℕ := b + 260
def cpFind : ℕ := b + 267
def cpTup : ℕ := b + 276
def cpMapSec : ℕ := b + 313
def cpSplit : ℕ := b + 316
def cpMapFst : ℕ := b + 328
def cpFstF : ℕ := b + 331
def cpApp : ℕ := b + 332
def cpKr : ℕ := b + 335
def cpRange : ℕ := b + 355
def cpMapInd : ℕ := b + 358
def cpCnt : ℕ := b + 361
def cpWp : ℕ := b + 366
def cpDom : ℕ := b + 381
def cpAnsG : ℕ := b + 406
def cpClos : ℕ := b + 414
def cpFilt : ℕ := b + 469

/-- **The move function**: inside a round or at its start. -/
def cpMvF : Expr := .ite (.length (cpKf 10)) (.call (b + 5) (.var 0)) (.call (b + 1) (.var 0))

/-- The program state of the next round, with no call: the stage `[ps, incP]` of the round
(`incP = .var 1`, empty here) is logged. -/
def cpSuccE : Expr :=
  Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, cpKf 5, cpKf 6,
    .arith .add (cpKf 7) (.nat 1), cpKf 8, cpKf 9, cpKf 10, cpKf 11,
    .snoc (cpKf 12) (mk2 (cpKf 8) (.var 1)), cpKf 13, cpKf 14]

/-- **The start of a round.** -/
def cpRoundF : Expr :=
  .ite (.arith .eq (cpKf 7) (cpPf 3))
    (.call (b + 2) (.var 0))
    (.letE (.call (cpInc b) (Expr.mkList [cpPf 1, cpKf 8, .get (cpKf 11) (.nat 1), cpPf 4, cpPf 4,
        cpKf 9]))
      (.ite (.length (.var 1))
        (.call (b + 3) (mk2 cpKs (.var 1)))
        (mk2 (.nat 2) (mk2 cpSuccE (.nat 0)))))

/-- The results after the loop of `y`. -/
def cpResE : Expr := .snoc (cpKf 3) (mk2 (cpKf 6) (cpKf 8))

/-- The logs after the loop of `y`: `[T, x-stages, y-stages]` is added. -/
def cpLogsE : Expr := .snoc (cpKf 14) (mk3 (cpKf 11) (cpKf 13) (cpKf 12))

/-- **The end of a string.** -/
def cpEndF : Expr :=
  .ite (cpKf 2)
    (.ite (.length (cpKf 1))
      (.letE (.call (cpPt b) (mk3 (cpPf 1) (cpPf 2) (.get (.get (cpKf 1) (.nat 0)) (.nat 0))))
        (.letE (.call (cpTail b) (cpKf 1))
          (mk2 (.nat 2) (mk2 (Expr.mkList [cpKf 0, .var 2, .nat 0, cpResE, cpKf 4, .var 1, cpKf 6,
            .nat 0, .var 1, cpPf 5, .nil, .get (cpKf 1) (.nat 0), .nil, .nil, cpLogsE])
            (.nat 0)))))
      (mk2 (.nat 0) (mk2 cpResE cpLogsE)))
    (mk2 (.nat 2) (mk2 (Expr.mkList [cpKf 0, cpKf 1, .nat 1, cpKf 3, cpKf 4, cpKf 5, cpKf 8,
      .nat 0, cpKf 5, cpPf 5, .nil, cpKf 11, .nil, cpKf 12, cpKf 14]) (.nat 0)))

/-- The key of the cache, on the kernel pairs `.var 1`. -/
def cpKeyE : Expr :=
  mk2 (.call (cpMkG b) (mk2 (cpPf 7) (.call (cpPEnc b) (mk2 (cpSf 0) (cpKf 8)))))
    (.call (cpMkG b) (mk2 (cpPf 7) (.call (cpPEnc b) (mk2 (cpSf 0) (.var 1)))))

/-- **The first window call of a round**, on `[kst, incP]`. -/
def cpStartF : Expr :=
  .letE (.call (cpStab b) (mk3 (cpPf 1) (cpKf 8) (.get (cpKf 11) (.nat 1))))
  (.letE (cpKeyE b)
  (.letE (.call (cpFind b) (mk2 (.var 2) (cpKf 4)))
  (.letE (.call (b + 4) (mk3 cpKs (.var 2) (.var 3)))
  (.letE (.call (cpKr b) (mk2 (cpSf 0) (.var 1)))
  (.letE (.call (b + 11) (mk2 (cpSf 0) (arg 1)))
  (.letE (.call (cpWp b) (mk3 (cpSf 2) cpZv (.get (.get (.var 4) (.nat 0)) (.nat 0))))
  (.letE (.call (cpTail b) (.get (.var 4) (.nat 0)))
    (Expr.mkList [.nat 1, .nat (modeCode .cont), cpWinE (.var 5) (.var 6) (.var 7),
      Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, .get (.var 4) (.nat 1), cpKf 5, cpKf 6, cpKf 7,
        cpKf 8, cpKf 9,
        Expr.mkList [.var 8, .nil, .var 5, .var 6, arg 1, .get (.get (.var 4) (.nat 0)) (.nat 0)],
        cpKf 11, cpKf 12, cpKf 13, cpKf 14]]))))))))

/-- **The representatives**, on `[kst, key, i]`: the cached ones, or new ones. Returns
`[reps, cache']`. -/
def cpRepsF : Expr :=
  .ite (.arith .lt (arg 2) (.length (cpKf 4)))
    (mk2 (.get (.get (cpKf 4) (arg 2)) (.nat 2)) (cpKf 4))
    (.letE (.call (cpTup b) (mk4 (cpPf 1) (cpKf 8) (.get (cpKf 11) (.nat 1)) (cpPf 4)))
    (.letE (.call (cpMapSec b) (mk2 (.nat 0) (.var 1)))
    (.letE (.call (cpSplit b) (mk2 (cpPf 6) (.var 2)))
    (.letE (.call (cpMapFst b) (mk2 (.nat 0) (.var 3)))
    (.letE (.call (cpApp b) (mk2 (mk1 (.snoc (arg 1) (.var 4))) (cpKf 4)))
      (mk2 (.var 4) (.var 5)))))))

/-- **Inside a round**, on `[kst, u]`. -/
def cpWinF : Expr :=
  .letE (.call (cpAnsG b) (mk2 (cpIf 5) (.get (.var 0) (.nat 1))))
  (.letE (.call (cpApp b) (mk2 (cpIf 1) (.var 1)))
    (.ite (.length (cpIf 0))
      (.call (b + 9) (mk2 cpKs (.var 2)))
      (.call (b + 10) (mk2 cpKs (.var 2)))))

/-- **The next window call of a round**, on `[kst, gens']`. -/
def cpNextF : Expr :=
  .letE (.call (cpWp b) (mk3 (cpSf 2) cpZv (.get (cpIf 0) (.nat 0))))
  (.letE (.call (cpTail b) (cpIf 0))
    (Expr.mkList [.nat 1, .nat (modeCode .cont), cpWinE (cpIf 2) (cpIf 3) (.var 1),
      Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, cpKf 5, cpKf 6, cpKf 7, cpKf 8, cpKf 9,
        Expr.mkList [.var 2, arg 1, cpIf 2, cpIf 3, cpIf 4, .get (cpIf 0) (.nat 0)], cpKf 11,
        cpKf 12, cpKf 13, cpKf 14]]))

/-- **The end of a round**, on `[kst, gens']`. -/
def cpCloseF : Expr :=
  .letE (.call (cpClos b) (mk3 (cpPf 1) (cpPf 2) (arg 1)))
  (.letE (.call (cpFilt b) (mk2 (cpIf 4) (cpKf 9)))
    (mk2 (.nat 2) (mk2 (Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, cpKf 4, cpKf 5, cpKf 6,
      .arith .add (cpKf 7) (.nat 1), .var 1, .var 2, .nil, cpKf 11,
      .snoc (cpKf 12) (mk2 (cpKf 8) (cpIf 4)), cpKf 13, cpKf 14]) (.nat 0))))

/-- The step of the map of second parts: on `[c, [key, g]]`, the permutation `g`. -/
def cpSecF : Expr := .get (arg 1) (.nat 1)

/-- The step of the indicator: on `[incP, i]`, the number of `i` in `incP`. -/
def cpIndStepF : Expr := .call (cpCnt b) (mk2 (arg 1) (arg 0))

/-- The test of the difference: on `[incP, x]`, whether `x` is not in `incP`. -/
def cpDiffTestF : Expr := .arith .eq (.call (cpCnt b) (mk2 (arg 1) (arg 0))) (.nat 0)

/-- **The window indicator**, on `[k, incP]`. -/
def cpIndF : Expr := .letE (.call (cpRange b) (arg 0)) (.call (cpMapInd b) (mk2 (arg 1) (.var 1)))

end Funs

open GI.Cited (PointwiseStab Preimage Membership) in
/-- **Where the move program and its modules sit.** -/
structure CpMvAt (P : Program) (b jp jpre jm : ℕ) : Prop where
  mv : P.funs[b]? = some (cpMvF b)
  round : P.funs[b + 1]? = some (cpRoundF b)
  fin : P.funs[b + 2]? = some (cpEndF b)
  start : P.funs[b + 3]? = some (cpStartF b)
  reps : P.funs[b + 4]? = some (cpRepsF b)
  win : P.funs[b + 5]? = some (cpWinF b)
  sec : P.funs[b + 6]? = some cpSecF
  indStep : P.funs[b + 7]? = some (cpIndStepF b)
  diffTest : P.funs[b + 8]? = some (cpDiffTestF b)
  next : P.funs[b + 9]? = some (cpNextF b)
  close : P.funs[b + 10]? = some (cpCloseF b)
  ind : P.funs[b + 11]? = some (cpIndF b)
  inc : P.HasAt (cpInc b) (incFuns (cpInc b) jp)
  stab : P.HasAt (cpStab b) (graphStabFuns (cpStab b) jp)
  pt : P.HasAt (cpPt b) (ptFuns (cpPt b) jpre)
  tail : P.HasAt (cpTail b) (tailFuns (cpTail b))
  pEnc : P.HasAt (cpPEnc b) (pEncMapFuns (cpPEnc b))
  mkG : P.HasAt (cpMkG b) (mkGroupFuns (cpMkG b))
  find : P.HasAt (cpFind b) (ckFindFuns (cpFind b) jm)
  tup : P.HasAt (cpTup b) (graphTupFuns (cpTup b))
  mapSec : P.HasAt (cpMapSec b) (mapFuns (cpMapSec b) (b + 6))
  split : P.HasAt (cpSplit b) (pSplitMapFuns (cpSplit b))
  mapFst : P.HasAt (cpMapFst b) (mapFuns (cpMapFst b) (cpFstF b))
  fstF : P.funs[cpFstF b]? = some krFstF
  app : P.HasAt (cpApp b) (appendFuns (cpApp b))
  kr : P.HasAt (cpKr b) (krFuns (cpKr b) jp)
  range : P.HasAt (cpRange b) (rangeFuns (cpRange b))
  mapInd : P.HasAt (cpMapInd b) (mapFuns (cpMapInd b) (b + 7))
  cnt : P.HasAt (cpCnt b) (countFuns (cpCnt b))
  wp : P.HasAt (cpWp b) (wpFuns (cpWp b) (cpDom b))
  dom : DomAt P (cpDom b)
  ansG : P.HasAt (cpAnsG b) (ansGensFuns (cpAnsG b))
  clos : P.HasAt (cpClos b) (closFuns (cpClos b) jpre)
  filt : P.HasAt (cpFilt b) (filterFuns (cpFilt b) (b + 8))

/-- **The function table of the move program**, at base `b` (472 functions). -/
def cpMvFuns (b jp jpre jm : ℕ) : List Expr :=
  [cpMvF b, cpRoundF b, cpEndF b, cpStartF b, cpRepsF b, cpWinF b, cpSecF, cpIndStepF b,
    cpDiffTestF b, cpNextF b, cpCloseF b, cpIndF b, .nat 0, .nat 0, .nat 0, .nat 0] ++
  incFuns (cpInc b) jp ++ graphStabFuns (cpStab b) jp ++ ptFuns (cpPt b) jpre ++
  tailFuns (cpTail b) ++ pEncMapFuns (cpPEnc b) ++ mkGroupFuns (cpMkG b) ++
  ckFindFuns (cpFind b) jm ++ graphTupFuns (cpTup b) ++ mapFuns (cpMapSec b) (b + 6) ++
  pSplitMapFuns (cpSplit b) ++ mapFuns (cpMapFst b) (cpFstF b) ++ [krFstF] ++
  appendFuns (cpApp b) ++ krFuns (cpKr b) jp ++ rangeFuns (cpRange b) ++
  mapFuns (cpMapInd b) (b + 7) ++ countFuns (cpCnt b) ++ wpFuns (cpWp b) (cpDom b) ++
  domFuns (cpDom b) ++ ansGensFuns (cpAnsG b) ++ closFuns (cpClos b) jpre ++
  filterFuns (cpFilt b) (b + 8)

end GI.Impl
