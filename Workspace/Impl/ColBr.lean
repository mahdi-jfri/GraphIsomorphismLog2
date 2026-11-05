module

public import Workspace.Impl.ColLevProg

@[expose] public section

/-!
# The column branch of the row step, as a program

When the group `N` of Theorem A.18 is not transitive on a row, the row step stores the columns and
continues (`Run.rowColumns`). The program `colBrF` does this on

`[sv, q, rows, σN, rl]`,

where `sv` is the canonical state value, `q` the number of rows, `rows` the coordinates of
Theorem A.17 (`coordsVal`), `σN` the generators of `N` that `a18_spec` returns, and `rl` the row
labels of the positions. It computes the value of the child state (`colChildE`) and calls
`Continue` on it. The child value is:

* the state value with a new hierarchy and a new row record, and `h - 1`;
* the hierarchy: for every stored level `k` the lower piece and the upper piece
  (`Workspace/Impl/ColLevProg.lean`), with the row interval `[cols, q, min cap_J q, origin_J]`
  between them, where `J` is the first stored level that does not refine the rows; the
  intervals of ratio below `2` are dropped (`colKeep`);
* the row record `[q, rl, [cols]]`.

The steps, in order: the positions `r0` of row `0` and `m = |r0|`; the orbit labels `ol` of `N`
(`orbits_spec`); the column coordinate `cf` of each position (`colInvF`); `oc = ol ∘ cf`; the
column labels; the switch test of each level (`colNotLowF`) and the first failing level `J`
(`findEq`); the two pieces of each level; the row interval; the filtered hierarchy.

This file gives the program and its value (`colChild_det`, cost `colBrK (X + 1)^5` for a bound
`X` on the numbers and weights). `Workspace/Impl/ColBrSpec.lean` proves that the value is a
canonical value of the child state of `Run.rowColumns`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

/-! ### The program -/

/-- On `[c, x]`: whether the ratio of the interval value `x` is at least `2`. -/
def colKeepF : Expr := .arith .lt (.nat 1) (.get (arg 1) (.nat 1))

/-- Entry `j` of the state value (entry `0` of the argument). -/
def colSvE (j : ℕ) : Expr := .get (arg 0) (.nat j)

/-- `min cap_J q` as `cap_J - (cap_J - q)`. -/
def colRowCapE : Expr :=
  .arith .sub (.get (.get (.var 10) (.var 13)) (.nat 2))
    (.arith .sub (.get (.get (.var 10) (.var 13)) (.nat 2)) (arg 1))

/-- The child value, from the environment of `colLevE` and the three pieces of the hierarchy at
`15`, `16`, `17`. -/
def colBodyE (b : ℕ) : Expr :=
  Expr.mkList [colSvE 0, colSvE 1, colSvE 2, colSvE 3, colSvE 4,
    .call (b + 42) (mk2 (.nat 0) (.call (b + 45) (mk2 (.snoc (.var 15) (.var 17)) (.var 16)))),
    mk1 (mk3 (arg 1) (arg 4) (mk1 (.var 9))),
    colSvE 7, .arith .sub (colSvE 8) (.nat 1), colSvE 9]

/-- The levels and the row interval, then the child value, from the first `13` values. -/
def colLevE (b : ℕ) : Expr :=
  .letE (Expr.mkList [.var 10, .var 2, .var 4, .var 8, .var 7, arg 4, colSvE 2, .var 5, .var 3,
      .var 1, .var 6])
  (.letE (.call (b + 36) (mk2 (.var 14) (.var 11)))
  (.letE (.call (b + 39) (mk2 (.var 14) (.var 11)))
  (.letE (mk4 (.var 9) (arg 1) colRowCapE (.get (.get (.var 10) (.var 13)) (.nat 3)))
  (colBodyE b))))

/-- **The value of the child state**, on `[sv, q, rows, σN, rl]`. The function table of the
module at `b` is `colBrFuns`. -/
def colChildE (b : ℕ) : Expr :=
  .letE (colSvE 0)
  (.letE (.get (arg 2) (.nat 0))
  (.letE (.length (.var 2))
  (.letE (.call (b + 79) (mk2 (.var 3) (arg 3)))
  (.letE (.call (b + 48) (.var 3))
  (.letE (.call (b + 48) (.var 1))
  (.letE (.call (b + 21) (mk2 (mk3 (colSvE 2) (arg 4) (arg 2)) (.var 6)))
  (.letE (.call (b + 12) (mk2 (mk3 (.var 4) (.var 7) (.nat 0)) (.var 6)))
  (.letE (.get (.call (b + 55) (mk2 (.call (b + 12) (mk2 (mk3 (.var 4) (.var 7)
      (.arith .add (.var 1) (.nat 1))) (.var 6))) (colSvE 2))) (.nat 2))
  (.letE (colSvE 5)
  (.letE (.call (b + 48) (.length (.var 10)))
  (.letE (.call (b + 30) (mk2 (.snoc (mk4 (.var 10) (colSvE 2) (arg 4) (.get (.var 2) (.nat 0)))
      (.var 6)) (.var 11)))
  (.letE (.call (b + 51) (mk2 (.nat 1) (.var 12)))
  (colLevE b)))))))))))))

/-- **The column branch**: call `Continue` (function `fc`) on the child value. -/
def colBrF (b fc : ℕ) : Expr := .call fc (colChildE b)

/-- **The module of the column branch** at `b` (111 functions); `Continue` is function `fc`. -/
def colBrFuns (b fc : ℕ) : List Expr :=
  [colBrF b fc, colLowF (b + 12) (b + 15) (b + 18) (b + 55),
    colUpF (b + 12) (b + 15) (b + 24) (b + 55), colPickF, colEqF, colKeyF, colInvF (b + 51),
    colMinF (b + 27), colMinStepF, colNotLowF (b + 33), colLowPosF, colKeepF] ++
  mapFuns (b + 12) (b + 3) ++ mapFuns (b + 15) (b + 4) ++ mapFuns (b + 18) (b + 5) ++
  mapFuns (b + 21) (b + 6) ++ mapFuns (b + 24) (b + 7) ++ iterFuns (b + 27) (b + 8) ++
  mapFuns (b + 30) (b + 9) ++ allFuns (b + 33) (b + 10) ++ mapFuns (b + 36) (b + 1) ++
  mapFuns (b + 39) (b + 2) ++ filterFuns (b + 42) (b + 11) ++ appendFuns (b + 45) ++
  rangeFuns (b + 48) ++ findEqFuns (b + 51) ++ clsFuns (b + 55) ++ orbitFuns (b + 79)

theorem length_colBrFuns (b fc : ℕ) : (colBrFuns b fc).length = 111 := by
  simp [colBrFuns, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns,
    findFuns, loopFuns, length_clsFuns, length_orbitFuns]

/-- **Where the functions of the module sit.** -/
structure ColBrAt (P : Program) (b fc : ℕ) : Prop where
  main : P.funs[b]? = some (colBrF b fc)
  low : P.funs[b + 1]? = some (colLowF (b + 12) (b + 15) (b + 18) (b + 55))
  up : P.funs[b + 2]? = some (colUpF (b + 12) (b + 15) (b + 24) (b + 55))
  pick : P.funs[b + 3]? = some colPickF
  eq : P.funs[b + 4]? = some colEqF
  key : P.funs[b + 5]? = some colKeyF
  inv : P.funs[b + 6]? = some (colInvF (b + 51))
  min : P.funs[b + 7]? = some (colMinF (b + 27))
  minStep : P.funs[b + 8]? = some colMinStepF
  notLow : P.funs[b + 9]? = some (colNotLowF (b + 33))
  lowPos : P.funs[b + 10]? = some colLowPosF
  keep : P.funs[b + 11]? = some colKeepF
  mPick : P.HasAt (b + 12) (mapFuns (b + 12) (b + 3))
  mEq : P.HasAt (b + 15) (mapFuns (b + 15) (b + 4))
  mKey : P.HasAt (b + 18) (mapFuns (b + 18) (b + 5))
  mInv : P.HasAt (b + 21) (mapFuns (b + 21) (b + 6))
  mMin : P.HasAt (b + 24) (mapFuns (b + 24) (b + 7))
  iter : P.HasAt (b + 27) (iterFuns (b + 27) (b + 8))
  mNot : P.HasAt (b + 30) (mapFuns (b + 30) (b + 9))
  all : P.HasAt (b + 33) (allFuns (b + 33) (b + 10))
  mLow : P.HasAt (b + 36) (mapFuns (b + 36) (b + 1))
  mUp : P.HasAt (b + 39) (mapFuns (b + 39) (b + 2))
  filt : P.HasAt (b + 42) (filterFuns (b + 42) (b + 11))
  app : P.HasAt (b + 45) (appendFuns (b + 45))
  rng : P.HasAt (b + 48) (rangeFuns (b + 48))
  fEq : P.HasAt (b + 51) (findEqFuns (b + 51))
  cls : P.HasAt (b + 55) (clsFuns (b + 55))
  orb : P.HasAt (b + 79) (orbitFuns (b + 79))

set_option linter.unusedSimpArgs false in
theorem colBrAt_of_hasAt {P : Program} {b fc : ℕ} (h : P.HasAt b (colBrFuns b fc)) :
    ColBrAt P b fc := by
  unfold colBrFuns at h
  have orb : P.HasAt (b + 79) (orbitFuns (b + 79)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have cls : P.HasAt (b + 55) (clsFuns (b + 55)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have fEq : P.HasAt (b + 51) (findEqFuns (b + 51)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have rng : P.HasAt (b + 48) (rangeFuns (b + 48)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have app : P.HasAt (b + 45) (appendFuns (b + 45)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have filt : P.HasAt (b + 42) (filterFuns (b + 42) (b + 11)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mUp : P.HasAt (b + 39) (mapFuns (b + 39) (b + 2)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mLow : P.HasAt (b + 36) (mapFuns (b + 36) (b + 1)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have all : P.HasAt (b + 33) (allFuns (b + 33) (b + 10)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mNot : P.HasAt (b + 30) (mapFuns (b + 30) (b + 9)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have iter : P.HasAt (b + 27) (iterFuns (b + 27) (b + 8)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mMin : P.HasAt (b + 24) (mapFuns (b + 24) (b + 7)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mInv : P.HasAt (b + 21) (mapFuns (b + 21) (b + 6)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mKey : P.HasAt (b + 18) (mapFuns (b + 18) (b + 5)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mEq : P.HasAt (b + 15) (mapFuns (b + 15) (b + 4)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have mPick : P.HasAt (b + 12) (mapFuns (b + 12) (b + 3)) := by
    have := h.right
    simp only [List.length_append, List.length_cons, List.length_nil, mapFuns, iterFuns, allFuns, filterFuns, appendFuns, rangeFuns, findEqFuns, findFuns, loopFuns, length_clsFuns, length_orbitFuns] at this
    exact this
  replace h := h.left
  have hd : ∀ j (hj : j < 12), _ := fun j hj => h j (by simpa using hj)
  exact {
    main := by simpa using hd 0 (by norm_num)
    low := by simpa using hd 1 (by norm_num)
    up := by simpa using hd 2 (by norm_num)
    pick := by simpa using hd 3 (by norm_num)
    eq := by simpa using hd 4 (by norm_num)
    key := by simpa using hd 5 (by norm_num)
    inv := by simpa using hd 6 (by norm_num)
    min := by simpa using hd 7 (by norm_num)
    minStep := by simpa using hd 8 (by norm_num)
    notLow := by simpa using hd 9 (by norm_num)
    lowPos := by simpa using hd 10 (by norm_num)
    keep := by simpa using hd 11 (by norm_num)
    mPick := mPick
    mEq := mEq
    mKey := mKey
    mInv := mInv
    mMin := mMin
    iter := iter
    mNot := mNot
    all := all
    mLow := mLow
    mUp := mUp
    filt := filt
    app := app
    rng := rng
    fEq := fEq
    cls := cls
    orb := orb
  }

end GI.Impl
