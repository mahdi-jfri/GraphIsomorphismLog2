module

public import Workspace.Impl.TermJSolStack

@[expose] public section

/-!
# Zero-sum solve and coefficient kernel (program layout)

Two entry functions share one installed Hermite row solver.

* `tmJSolSolveF`, on `[encIntMatrix M, encIntMatrix B, linVecVal s]`: stack `M` above `B`,
  negate `s`, call the row solver `linRowSolverF` on `[M; B]` and `-s`, and keep the last `G`
  entries of the solution (the coefficients on the rows of `B`).
* `tmJSolKerF`, on `[encIntMatrix M, encIntMatrix B]`: stack, call the Hermite primitive, and
  keep the last `G` coordinates of the last `G` rows of the unimodular multiplier `U`.

`tmJSolFuns b j` holds all 67 functions at `b, …, b + 66`; the Hermite primitive sits at
primitive index `j`. `tmJSolAt.of_hasAt` reads off where each piece sits.
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix)
set_option maxHeartbeats 4000000

/-- On `[M, B, s]`. Variables 1–3: the Hermite input, `-s`, the solver's answer. -/
def tmJSolSolveF (st sc rs dr : ℕ) : Expr :=
  .letE (.call st (.var 0))
    (.letE (.call sc (mk2 linIntMinusOneE (arg 2)))
      (.letE (.call rs (mk2 (.var 1) (.var 2)))
        (.ite (.isNat (.var 3)) (.nat 0)
          (mk2 (.nat 1) (.call dr (mk2 (.length (arg 0)) (.get (.var 3) (.nat 1))))))))

/-- On `[M, B]`. Variables 1–2: the Hermite input and the Hermite output `[U, H]`. -/
def tmJSolKerF (st her km dr : ℕ) : Expr :=
  .letE (.call st (.var 0))
    (.letE (.call her (.var 1))
      (.call km (mk2 (.length (arg 0))
        (.call dr (mk2 (.length (arg 0)) (.get (.var 2) (.nat 0)))))))

/-- The triangular-substitution indices of the installed solver. -/
def tmJSolTI (b : ℕ) : linTriIndices :=
  ⟨b + 49, b + 17, b + 18, b + 21, b + 22, b + 26, b + 29, b + 32⟩

/-- The lift indices of the installed solver. -/
def tmJSolLI (b : ℕ) : linLiftIndices :=
  ⟨b + 35, b + 36, b + 32, b + 39, b + 42, b + 46, b + 49⟩

/-- All functions, at `b, …, b + 66`. -/
def tmJSolFuns (b j : ℕ) : List Expr :=
  [tmJSolSolveF (b + 2) (b + 26) (b + 9) (b + 3), tmJSolKerF (b + 2) (b + 10) (b + 6) (b + 3),
    tmJSolStackF (b + 32)] ++ (
  tmJSolDropFuns (b + 3) ++ (mapFuns (b + 6) (b + 3) ++ (
  [linRowSolverF (b + 10) (b + 11), linHermiteF j,
    linHermiteFinishF (b + 12) (b + 15) (b + 16)] ++ (
  linTakeFuns (b + 12) ++ (
  [linTriUpperF (b + 15) (tmJSolTI b), linHermiteLiftF (tmJSolLI b),
    linIntExactF (b + 49 + 14) (b + 49 + 15)] ++ (
  linTailFuns (b + 18) ++ ([linTrimF (b + 18) (b + 22)] ++ (linTrimMapFuns (b + 22) (b + 18) ++ (
  linVectorScaleFuns (b + 26) (b + 49) ++ (linVectorBinaryFuns (b + 29) (b + 49 + 12) ++ (
  appendFuns (b + 32) ++ ([linPadF (b + 36) (b + 32)] ++ (replicateFuns (b + 36) ++ (
  linRowMulFuns (b + 39) (b + 42) (b + 46) ++ (linColumnFuns (b + 42) ++ (
  linDotLoopFuns (b + 46) (b + 49) ++ linIntFuns (b + 49)))))))))))))))))

theorem tmJSolFuns_length (b j : ℕ) : (tmJSolFuns b j).length = 67 := rfl

/-- Where the pieces sit. -/
structure tmJSolAt (P : Program) (b j : ℕ) : Prop where
  solve : P.funs[b]? = some (tmJSolSolveF (b + 2) (b + 26) (b + 9) (b + 3))
  ker : P.funs[b + 1]? = some (tmJSolKerF (b + 2) (b + 10) (b + 6) (b + 3))
  stack : P.funs[b + 2]? = some (tmJSolStackF (b + 32))
  drop : P.HasAt (b + 3) (tmJSolDropFuns (b + 3))
  kmap : P.HasAt (b + 6) (mapFuns (b + 6) (b + 3))
  rs : P.funs[b + 9]? = some (linRowSolverF (b + 10) (b + 11))
  her : P.funs[b + 10]? = some (linHermiteF j)
  fin : P.funs[b + 11]? = some (linHermiteFinishF (b + 12) (b + 15) (b + 16))
  take : P.HasAt (b + 12) (linTakeFuns (b + 12))
  triF : P.funs[b + 15]? = some (linTriUpperF (b + 15) (tmJSolTI b))
  liftF : P.funs[b + 16]? = some (linHermiteLiftF (tmJSolLI b))
  tri : linTriInstalled P (tmJSolTI b)
  lift : linLiftInstalled P (tmJSolLI b)
  scale : P.HasAt (b + 26) (linVectorScaleFuns (b + 26) (b + 49))
  app : P.HasAt (b + 32) (appendFuns (b + 32))
  ints : linIntSpec P (b + 49)

set_option maxRecDepth 8000 in
/-- The functions `tmJSolFuns b j` at `b` give `tmJSolAt`. -/
theorem tmJSolAt.of_hasAt {P : Program} {b j : ℕ} (h : P.HasAt b (tmJSolFuns b j)) :
    tmJSolAt P b j := by
  have hints : linIntSpec P (b + 49) := linInt_spec (h.block 49 rfl)
  have happ : P.HasAt (b + 32) (appendFuns (b + 32)) := h.block 32 rfl
  exact {
    solve := (h.block (gs := [tmJSolSolveF (b + 2) (b + 26) (b + 9) (b + 3)]) 0 rfl).single
    ker := (h.block (gs := [tmJSolKerF (b + 2) (b + 10) (b + 6) (b + 3)]) 1 rfl).single
    stack := (h.block (gs := [tmJSolStackF (b + 32)]) 2 rfl).single
    drop := h.block 3 rfl
    kmap := h.block 6 rfl
    rs := (h.block (gs := [linRowSolverF (b + 10) (b + 11)]) 9 rfl).single
    her := (h.block (gs := [linHermiteF j]) 10 rfl).single
    fin := (h.block (gs := [linHermiteFinishF (b + 12) (b + 15) (b + 16)]) 11 rfl).single
    take := h.block 12 rfl
    triF := (h.block (gs := [linTriUpperF (b + 15) (tmJSolTI b)]) 15 rfl).single
    liftF := (h.block (gs := [linHermiteLiftF (tmJSolLI b)]) 16 rfl).single
    tri := {
      ints := hints
      exactDiv := (h.block (gs := [linIntExactF (b + 49 + 14) (b + 49 + 15)]) 17 rfl).single
      tail := h.block 18 rfl
      trim := (h.block (gs := [linTrimF (b + 18) (b + 22)]) 21 rfl).single
      trimMap := h.block 22 rfl
      scale := h.block 26 rfl
      sub := h.block 29 rfl
      append := happ }
    lift := {
      pad := (h.block (gs := [linPadF (b + 36) (b + 32)]) 35 rfl).single
      rep := h.block 36 rfl
      append := happ
      row := h.block 39 rfl
      column := h.block 42 rfl
      dot := h.block 46 rfl
      ints := hints }
    scale := h.block 26 rfl
    app := happ
    ints := hints }

end GI.Impl
