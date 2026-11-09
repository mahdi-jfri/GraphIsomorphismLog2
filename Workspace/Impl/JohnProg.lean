module

public import Workspace.Lang.Lib.Orbit
public import Workspace.Lang.Lib.NatList
public import Workspace.Lang.Lib.Search
public import Workspace.Lang.Lib.Fold

@[expose] public section

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

/-- The step of `johnMain` that finds `δ`: the label that occurs most often in row `0`. -/
def johnDeltaE : Expr := .get (.var 8) (.call 62 (mk2 (.call 57 (.var 9)) (.var 9)))

/-- The main function with the step `δE` for `δ`, on `[[n, gens], m, k]`. The environment grows by one value per `letE`:
`1: G, 2: n, 3: n * n, 4: R2, 5: pg, 6: lab, 7: Rn, 8: row, 9: cnt, 10: δ, 11: υ, 12: D, 13: Λ`. -/
def johnMainG (δE : Expr) : Expr :=
  .letE (.get (.var 0) (.nat 0)) <|
  .letE (.get (.var 1) (.nat 0)) <|
  .letE (.arith .mul (.var 2) (.var 2)) <|
  .letE (.call 1 (.var 3)) <|
  .letE (.call 4 (mk2 (mk2 (.var 2) (.var 4)) (.get (.var 1) (.nat 1)))) <|
  .letE (.call 12 (mk2 (.var 3) (.var 5))) <|
  .letE (.call 1 (.var 2)) <|
  .letE (.call 44 (mk2 (.var 6) (.var 7))) <|
  .letE (.call 48 (mk2 (.var 8) (.var 8))) <|
  .letE δE <|
  .letE (.get (.var 8) (.call 62 (mk2 (.arith .mul (.get (.var 0) (.nat 2))
    (.arith .sub (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2)))) (.var 9)))) <|
  .letE (.call 66 (mk2 (mk4 (.var 6) (.var 2) (.var 10) (.var 7)) (.var 7))) <|
  .letE (.call 74 (mk3 (.snoc (mk4 (.var 12) (.var 6) (.var 2) (.var 11)) (.var 7)) (.var 4) .nil))
    (.call 98 (mk2 (mk2 (.var 13) (.call 1 (.length (.var 13)))) (.var 7)))

/-- The main function, on `[[n, gens], m, k]`. -/
def johnMain : Expr := johnMainG johnDeltaE

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

/-- **The functions of the program after the main function**, at indices `1, …, 105`. The specs of
the parts hold in every program with these functions; the main function at `0` may differ. -/
class JohnAt (P : Program) : Prop where
  tail : P.HasAt 1 johnFuns.tail

instance : JohnAt johnProgram := ⟨by simpa using john_hasAt.block 1 rfl⟩

variable {P : Program} [JohnAt P]

theorem john_at_range : P.HasAt 1 (rangeFuns 1) := by
  simpa using (JohnAt.tail (P := P)).block 0 rfl

theorem john_at_mapPg : P.HasAt 4 (mapFuns 4 7) := by
  simpa using (JohnAt.tail (P := P)).block 3 rfl

theorem john_at_pgF : P.HasAt 7 ([johnPgF]) := by
  simpa using (JohnAt.tail (P := P)).block 6 rfl

theorem john_at_mapPgE : P.HasAt 8 (mapFuns 8 11) := by
  simpa using (JohnAt.tail (P := P)).block 7 rfl

theorem john_at_pgE : P.HasAt 11 ([johnPgE]) := by
  simpa using (JohnAt.tail (P := P)).block 10 rfl

theorem john_at_orbit : P.HasAt 12 (orbitFuns 12) := by
  simpa using (JohnAt.tail (P := P)).block 11 rfl

theorem john_at_gather : P.HasAt 44 (gatherFuns 44) := by
  simpa using (JohnAt.tail (P := P)).block 43 rfl

theorem john_at_mapCnt : P.HasAt 48 (mapFuns 48 51) := by
  simpa using (JohnAt.tail (P := P)).block 47 rfl

theorem john_at_cntF : P.HasAt 51 ([johnCntF]) := by
  simpa using (JohnAt.tail (P := P)).block 50 rfl

theorem john_at_count : P.HasAt 52 (countFuns 52) := by
  simpa using (JohnAt.tail (P := P)).block 51 rfl

theorem john_at_max : P.HasAt 57 (maxFuns 57) := by
  simpa using (JohnAt.tail (P := P)).block 56 rfl

theorem john_at_findEq : P.HasAt 62 (findEqFuns 62) := by
  simpa using (JohnAt.tail (P := P)).block 61 rfl

theorem john_at_mapRowD : P.HasAt 66 (mapFuns 66 69) := by
  simpa using (JohnAt.tail (P := P)).block 65 rfl

theorem john_at_rowDF : P.HasAt 69 ([johnRowDF]) := by
  simpa using (JohnAt.tail (P := P)).block 68 rfl

theorem john_at_mapEntD : P.HasAt 70 (mapFuns 70 73) := by
  simpa using (JohnAt.tail (P := P)).block 69 rfl

theorem john_at_entDF : P.HasAt 73 ([johnEntDF]) := by
  simpa using (JohnAt.tail (P := P)).block 72 rfl

theorem john_at_fold : P.HasAt 74 (foldlFuns 74 77) := by
  simpa using (JohnAt.tail (P := P)).block 73 rfl

theorem john_at_stepF : P.HasAt 77 ([johnStepF]) := by
  simpa using (JohnAt.tail (P := P)).block 76 rfl

theorem john_at_compCF : P.HasAt 78 ([johnCompCF]) := by
  simpa using (JohnAt.tail (P := P)).block 77 rfl

theorem john_at_filterB : P.HasAt 79 (filterFuns 79 82) := by
  simpa using (JohnAt.tail (P := P)).block 78 rfl

theorem john_at_bF : P.HasAt 82 ([johnBF]) := by
  simpa using (JohnAt.tail (P := P)).block 81 rfl

theorem john_at_mapC : P.HasAt 83 (mapFuns 83 86) := by
  simpa using (JohnAt.tail (P := P)).block 82 rfl

theorem john_at_cF : P.HasAt 86 ([johnCF]) := by
  simpa using (JohnAt.tail (P := P)).block 85 rfl

theorem john_at_allA : P.HasAt 87 (allFuns 87 90) := by
  simpa using (JohnAt.tail (P := P)).block 86 rfl

theorem john_at_aF : P.HasAt 90 ([johnAF]) := by
  simpa using (JohnAt.tail (P := P)).block 89 rfl

theorem john_at_anyEq : P.HasAt 91 (anyFuns 91 94) := by
  simpa using (JohnAt.tail (P := P)).block 90 rfl

theorem john_at_eqF : P.HasAt 94 ([johnEqF]) := by
  simpa using (JohnAt.tail (P := P)).block 93 rfl

theorem john_at_eqNats : P.HasAt 95 (eqNatsFuns 95) := by
  simpa using (JohnAt.tail (P := P)).block 94 rfl

theorem john_at_mapOut : P.HasAt 98 (mapFuns 98 101) := by
  simpa using (JohnAt.tail (P := P)).block 97 rfl

theorem john_at_outF : P.HasAt 101 ([johnOutF]) := by
  simpa using (JohnAt.tail (P := P)).block 100 rfl

theorem john_at_filterOut : P.HasAt 102 (filterFuns 102 105) := by
  simpa using (JohnAt.tail (P := P)).block 101 rfl

theorem john_at_outP : P.HasAt 105 ([johnOutP]) := by
  simpa using (JohnAt.tail (P := P)).block 104 rfl

end GI.Impl
