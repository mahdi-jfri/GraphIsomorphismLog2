module

public import Workspace.Impl.JohnMain
public import Workspace.Degree.JohnBall

@[expose] public section

/-!
# The Johnson identification program for `3k ≤ m`

The program `johnRProgram` is `johnProgram` with one step changed: the step that finds `Δ`
(`johnDeltaE`) becomes the ball search `johnDeltaRE` of `Degree/JohnBall.lean`. The other
functions of `johnProgram` stay at their indices `1, …, 105`, so the specs of `Impl/John*` hold for
it (the instance `JohnAt johnRProgram`). The search adds the functions `106, …, 117`.

* `106`: iterate `johnBallStepF` (`iterFuns`).
* `109`: `johnBallStepF`, on `[[U, Rn], i, R]`, one step of the ball.
* `110`: map `johnBallEntF` over the points (`mapFuns`).
* `113`: `johnBallEntF`, on `[[U, R, Rn], z]`, the new entry of `z`.
* `114`: whether some point passes `johnBallTestF` (`anyFuns`).
* `117`: `johnBallTestF`, on `[[U[z], R], y]`, the number `U[z][y] * R[y]`.

Here `U = johnDV n labL υ` is the matrix of the graph `Υ` and `R` is the ball as a list of `0`s
and `1`s.
-/

namespace GI.Degree

open GI.Lang GI.Cited GI.Proved GI.Impl Equiv
open GI.Machine (BinOp)

/-- The test of the search: on `[[U[z], R], y]`, the number `U[z][y] * R[y]`. -/
def johnBallTestF : Expr :=
  .arith .mul (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (.get (arg 0) (.nat 1)) (arg 1))

/-- The new entry of the ball: on `[[U, R, Rn], z]`, `1` if `R[z] ≠ 0`, and otherwise whether
some `y` has `U[z][y] * R[y] ≠ 0`. -/
def johnBallEntF : Expr :=
  .ite (.get (.get (arg 0) (.nat 1)) (arg 1)) (.nat 1)
    (.call 114 (mk2 (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))
      (.get (arg 0) (.nat 2))))

/-- One step of the ball: on `[[U, Rn], i, R]`, the next ball. -/
def johnBallStepF : Expr :=
  .call 110 (mk2 (mk3 (.get (arg 0) (.nat 0)) (arg 2) (.get (arg 0) (.nat 1)))
    (.get (arg 0) (.nat 1)))

/-- **The step `δ` by the ball search**, in the environment of `johnMainG` (`0` the input,
`2` the number `n`, `6` the labels, `7` the list `0, …, n - 1`, `8` the row `0`, `9` its counts).
It finds `υ` as the step after it does, then the matrix `U` of `υ`, the ball of radius `0`, the
ball of radius `k - 1`, and the label of `0` and the first point outside it. -/
def johnDeltaRE : Expr :=
  .letE (.get (.var 8) (.call 62 (mk2 (.arith .mul (.get (.var 0) (.nat 2))
    (.arith .sub (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)))) (.var 9)))) <|
  .letE (.call 66 (mk2 (mk4 (.var 6) (.var 2) (.var 10) (.var 7)) (.var 7))) <|
  .letE (.call 70 (mk2 (mk4 (.var 6) (.var 2) (.get (.var 6) (.nat 0)) (.nat 0)) (.var 7))) <|
  .letE (.call 106 (mk3 (mk2 (.var 11) (.var 7)) (.arith .sub (.get (.var 0) (.nat 2)) (.nat 1))
    (.var 12))) <|
  .get (.var 8) (.call 62 (mk2 (.nat 0) (.var 13)))

/-- The functions of the search, at indices `106, …, 117`. -/
def johnRExtra : List Expr :=
  iterFuns 106 109 ++ [johnBallStepF] ++ mapFuns 110 113 ++ [johnBallEntF] ++ anyFuns 114 117 ++
    [johnBallTestF]

/-- **The function table.** -/
def johnRFuns : List Expr := [johnMainG johnDeltaRE] ++ johnFuns.tail ++ johnRExtra

/-- The program: no primitives. -/
def johnRProgram : Program := ⟨johnRFuns, []⟩

instance : JohnAt johnRProgram :=
  ⟨Program.hasAt_append [johnMainG johnDeltaRE] johnFuns.tail johnRExtra []⟩

theorem johnR_main : johnRProgram.funs[0]? = some (johnMainG johnDeltaRE) := rfl

theorem johnR_hasAt : johnRProgram.HasAt 106 johnRExtra := by
  have h := Program.hasAt_append ([johnMainG johnDeltaRE] ++ johnFuns.tail) johnRExtra [] []
  have hl : ([johnMainG johnDeltaRE] ++ johnFuns.tail).length = 106 := by
    simp [john_length]
  rw [hl, List.append_nil] at h
  exact h

theorem johnR_at_iter : johnRProgram.HasAt 106 (iterFuns 106 109) := by
  simpa using johnR_hasAt.block 0 rfl

theorem johnR_at_step : johnRProgram.HasAt 109 [johnBallStepF] := by
  simpa using johnR_hasAt.block 3 rfl

theorem johnR_at_map : johnRProgram.HasAt 110 (mapFuns 110 113) := by
  simpa using johnR_hasAt.block 4 rfl

theorem johnR_at_ent : johnRProgram.HasAt 113 [johnBallEntF] := by
  simpa using johnR_hasAt.block 7 rfl

theorem johnR_at_any : johnRProgram.HasAt 114 (anyFuns 114 117) := by
  simpa using johnR_hasAt.block 8 rfl

theorem johnR_at_test : johnRProgram.HasAt 117 [johnBallTestF] := by
  simpa using johnR_hasAt.block 11 rfl

end GI.Degree
