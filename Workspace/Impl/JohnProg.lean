import Workspace.Lang.Lib.Orbit
import Workspace.Lang.Lib.NatList
import Workspace.Lang.Lib.Search
import Workspace.Lang.Lib.Fold

/-!
# The program for the Johnson identification

The program follows [H, §2.8] (see `Workspace/Proved/JohnLambda.lean`). On the input
`[encPerms (1 :: gs), m, k]` it

1. builds the action of each generator on the pairs, as a permutation of `Fin (n * n)` (`pgF`);
2. computes the orbit labels of the pairs with the library (`orbitFuns`);
3. reads row `0` of the labels, counts each label in it, and takes the label `Δ` that occurs most
   often and the label `Υ` that occurs `k (m - k)` times;
4. builds the 0/1 matrix `D` of the pairs with label `Δ` (`rowDF`, `entDF`);
5. runs over the pairs `p = n * x + y` with label `Υ`, computes `C(x, y)` (`compCF`), and keeps
   it if it is new (`stepF`);
6. lists, for each point `x`, the indices of the kept sets that contain `x` (`outF`).

The functions sit at fixed indices; the table is `johnFuns`, with 106 functions.
-/

namespace GI.Impl

open GI.Lang

/-- The entry of a pair generator: on `[[g, n], p]`, the number `n * g(p / n) + g(p % n)`. -/
def johnPgE : Expr :=
  .arith .add
    (.arith .mul (.get (arg 0) (.nat 1))
      (.get (.get (arg 0) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 1)))))
    (.get (.get (arg 0) (.nat 0)) (.arith .mod (arg 1) (.get (arg 0) (.nat 1))))

/-- A pair generator: on `[[n, R2], g]`, the map of `johnPgE` over `R2 = [0, …, n * n - 1]`. -/
def johnPgF : Expr := .call 8 (mk2 (mk2 (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 1)))

/-- The count of an entry: on `[row, j]`, the number of entries of `row` equal to `j`. -/
def johnCntF : Expr := .call 52 (mk2 (arg 1) (arg 0))

/-- A row of the matrix `D`: on `[[lab, n, δ, Rn], x]`, the map of `johnEntDF` over `Rn`. -/
def johnRowDF : Expr :=
  .call 70 (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))
    (arg 1)) (.get (arg 0) (.nat 3)))

/-- An entry of `D`: on `[[lab, n, δ, x], y]`, whether `lab[n * x + y] = δ`. -/
def johnEntDF : Expr :=
  .arith .eq
    (.get (.get (arg 0) (.nat 0))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 3))) (arg 1)))
    (.get (arg 0) (.nat 2))

/-- One step over the pairs: on `[[D, lab, n, υ, Rn], acc, p]`. If `lab[p] = υ`, compute
`C = C(p / n, p % n)` and add it to `acc` unless it is there. -/
def johnStepF : Expr :=
  .ite (.arith .eq (.get (.get (arg 0) (.nat 1)) (arg 2)) (.get (arg 0) (.nat 3)))
    (.letE (.call 78 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 4))
        (.arith .div (arg 2) (.get (arg 0) (.nat 2))) (.arith .mod (arg 2) (.get (arg 0) (.nat 2)))))
      (.ite (.call 91 (mk2 (.var 1) (arg 1))) (arg 1) (.snoc (arg 1) (.var 1))))
    (arg 1)

/-- The set `C(x, y)`: on `[D, Rn, x, y]`, first `B = B(x, y)`, then the map of `johnCF`. -/
def johnCompCF : Expr :=
  .letE (.call 79 (mk2 (mk3 (arg 0) (arg 2) (arg 3)) (arg 1)))
    (.call 83 (mk2 (mk2 (arg 0) (.var 1)) (arg 1)))

/-- The test of `B(x, y)`: on `[[D, x, y], z]`, the value `¬ D[x][z] ∧ D[y][z]`. -/
def johnBF : Expr :=
  .ite (.get (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1)) (.nat 0)
    (.get (.get (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2))) (arg 1))

/-- An entry of `C(x, y)`: on `[[D, B], r]`, whether `¬ D[z][r]` for all `z ∈ B`. -/
def johnCF : Expr := .call 87 (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The test of `johnCF`: on `[[D, r], z]`, the value `1 - D[z][r]`. -/
def johnAF : Expr :=
  .arith .sub (.nat 1) (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The test of the search for a set: on `[C, v]`, whether `v = C`. -/
def johnEqF : Expr := .call 95 (mk2 (arg 1) (arg 0))

/-- A row of the output: on `[[Λ, RL], x]`, the indices `t ∈ RL` with `Λ[t][x] = 1`. -/
def johnOutF : Expr :=
  .call 102 (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The test of `johnOutF`: on `[[Λ, x], t]`, whether `Λ[t][x] = 1`. -/
def johnOutP : Expr :=
  .arith .eq (.get (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))) (.nat 1)

/-- The main function, on `[[n, gens], m, k]`. The environment grows by one value per `letE`:
`1: G, 2: n, 3: n * n, 4: R2, 5: pg, 6: lab, 7: Rn, 8: row, 9: cnt, 10: δ, 11: υ, 12: D, 13: Λ`. -/
def johnMain : Expr :=
  .letE (.get (.var 0) (.nat 0)) <|
  .letE (.get (.var 1) (.nat 0)) <|
  .letE (.arith .mul (.var 2) (.var 2)) <|
  .letE (.call 1 (.var 3)) <|
  .letE (.call 4 (mk2 (mk2 (.var 2) (.var 4)) (.get (.var 1) (.nat 1)))) <|
  .letE (.call 12 (mk2 (.var 3) (.var 5))) <|
  .letE (.call 1 (.var 2)) <|
  .letE (.call 44 (mk2 (.var 6) (.var 7))) <|
  .letE (.call 48 (mk2 (.var 8) (.var 8))) <|
  .letE (.get (.var 8) (.call 62 (mk2 (.call 57 (.var 9)) (.var 9)))) <|
  .letE (.get (.var 8) (.call 62 (mk2 (.arith .mul (.get (.var 0) (.nat 2))
    (.arith .sub (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)))) (.var 9)))) <|
  .letE (.call 66 (mk2 (mk4 (.var 6) (.var 2) (.var 10) (.var 7)) (.var 7))) <|
  .letE (.call 74 (mk3 (.snoc (mk4 (.var 12) (.var 6) (.var 2) (.var 11)) (.var 7)) (.var 4) .nil))
    (.call 98 (mk2 (mk2 (.var 13) (.call 1 (.length (.var 13)))) (.var 7)))

/-- **The function table.** -/
def johnFuns : List Expr :=
  [johnMain] ++ rangeFuns 1 ++ mapFuns 4 7 ++ [johnPgF] ++ mapFuns 8 11 ++ [johnPgE] ++
    orbitFuns 12 ++ gatherFuns 44 ++ mapFuns 48 51 ++ [johnCntF] ++ countFuns 52 ++ maxFuns 57 ++
    findEqFuns 62 ++ mapFuns 66 69 ++ [johnRowDF] ++ mapFuns 70 73 ++ [johnEntDF] ++
    foldlFuns 74 77 ++ [johnStepF] ++ [johnCompCF] ++ filterFuns 79 82 ++ [johnBF] ++
    mapFuns 83 86 ++ [johnCF] ++ allFuns 87 90 ++ [johnAF] ++ anyFuns 91 94 ++ [johnEqF] ++
    eqNatsFuns 95 ++ mapFuns 98 101 ++ [johnOutF] ++ filterFuns 102 105 ++ [johnOutP]

/-- The program: no primitives. -/
def johnProgram : Program := ⟨johnFuns, []⟩

theorem john_hasAt : johnProgram.HasAt 0 johnFuns := fun j hj => by
  simp only [johnProgram, Nat.zero_add, List.getElem?_eq_getElem hj]

theorem john_length : johnFuns.length = 106 := by
  simp [johnFuns, rangeFuns, mapFuns, loopFuns, orbitFuns, rangeFuns, invMapFuns, invFuns,
    findFuns, iterFuns, roundFoldFuns, foldlFuns, minMapFuns, gatherFuns, countFuns, filterFuns,
    maxFuns, findEqFuns, allFuns, anyFuns, eqNatsFuns]

theorem john_at_range : johnProgram.HasAt 1 (rangeFuns 1) := by
  simpa using john_hasAt.block 1 rfl

theorem john_at_mapPg : johnProgram.HasAt 4 (mapFuns 4 7) := by
  simpa using john_hasAt.block 4 rfl

theorem john_at_pgF : johnProgram.HasAt 7 ([johnPgF]) := by
  simpa using john_hasAt.block 7 rfl

theorem john_at_mapPgE : johnProgram.HasAt 8 (mapFuns 8 11) := by
  simpa using john_hasAt.block 8 rfl

theorem john_at_pgE : johnProgram.HasAt 11 ([johnPgE]) := by
  simpa using john_hasAt.block 11 rfl

theorem john_at_orbit : johnProgram.HasAt 12 (orbitFuns 12) := by
  simpa using john_hasAt.block 12 rfl

theorem john_at_gather : johnProgram.HasAt 44 (gatherFuns 44) := by
  simpa using john_hasAt.block 44 rfl

theorem john_at_mapCnt : johnProgram.HasAt 48 (mapFuns 48 51) := by
  simpa using john_hasAt.block 48 rfl

theorem john_at_cntF : johnProgram.HasAt 51 ([johnCntF]) := by
  simpa using john_hasAt.block 51 rfl

theorem john_at_count : johnProgram.HasAt 52 (countFuns 52) := by
  simpa using john_hasAt.block 52 rfl

theorem john_at_max : johnProgram.HasAt 57 (maxFuns 57) := by
  simpa using john_hasAt.block 57 rfl

theorem john_at_findEq : johnProgram.HasAt 62 (findEqFuns 62) := by
  simpa using john_hasAt.block 62 rfl

theorem john_at_mapRowD : johnProgram.HasAt 66 (mapFuns 66 69) := by
  simpa using john_hasAt.block 66 rfl

theorem john_at_rowDF : johnProgram.HasAt 69 ([johnRowDF]) := by
  simpa using john_hasAt.block 69 rfl

theorem john_at_mapEntD : johnProgram.HasAt 70 (mapFuns 70 73) := by
  simpa using john_hasAt.block 70 rfl

theorem john_at_entDF : johnProgram.HasAt 73 ([johnEntDF]) := by
  simpa using john_hasAt.block 73 rfl

theorem john_at_fold : johnProgram.HasAt 74 (foldlFuns 74 77) := by
  simpa using john_hasAt.block 74 rfl

theorem john_at_stepF : johnProgram.HasAt 77 ([johnStepF]) := by
  simpa using john_hasAt.block 77 rfl

theorem john_at_compCF : johnProgram.HasAt 78 ([johnCompCF]) := by
  simpa using john_hasAt.block 78 rfl

theorem john_at_filterB : johnProgram.HasAt 79 (filterFuns 79 82) := by
  simpa using john_hasAt.block 79 rfl

theorem john_at_bF : johnProgram.HasAt 82 ([johnBF]) := by
  simpa using john_hasAt.block 82 rfl

theorem john_at_mapC : johnProgram.HasAt 83 (mapFuns 83 86) := by
  simpa using john_hasAt.block 83 rfl

theorem john_at_cF : johnProgram.HasAt 86 ([johnCF]) := by
  simpa using john_hasAt.block 86 rfl

theorem john_at_allA : johnProgram.HasAt 87 (allFuns 87 90) := by
  simpa using john_hasAt.block 87 rfl

theorem john_at_aF : johnProgram.HasAt 90 ([johnAF]) := by
  simpa using john_hasAt.block 90 rfl

theorem john_at_anyEq : johnProgram.HasAt 91 (anyFuns 91 94) := by
  simpa using john_hasAt.block 91 rfl

theorem john_at_eqF : johnProgram.HasAt 94 ([johnEqF]) := by
  simpa using john_hasAt.block 94 rfl

theorem john_at_eqNats : johnProgram.HasAt 95 (eqNatsFuns 95) := by
  simpa using john_hasAt.block 95 rfl

theorem john_at_mapOut : johnProgram.HasAt 98 (mapFuns 98 101) := by
  simpa using john_hasAt.block 98 rfl

theorem john_at_outF : johnProgram.HasAt 101 ([johnOutF]) := by
  simpa using john_hasAt.block 101 rfl

theorem john_at_filterOut : johnProgram.HasAt 102 (filterFuns 102 105) := by
  simpa using john_hasAt.block 102 rfl

theorem john_at_outP : johnProgram.HasAt 105 ([johnOutP]) := by
  simpa using john_hasAt.block 105 rfl

end GI.Impl
