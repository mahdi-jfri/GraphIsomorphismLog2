import Workspace.Impl.TermRecProgList
import Workspace.Impl.TermRecSpec
import Workspace.Impl.TermSupFix
import Workspace.Impl.Combine
import Workspace.Lang.Prims.Reduce

/-!
# The recursion of Theorem A.20 as a `GI.Lang` program (T5)

`tmRiFuns b jsci jder jmem gObj` is the code of the recursion, at index `b`, with the cited
primitives **SolvableCosetIntersection** (`jsci`), **DerivedSubgroup** (`jder`) and
**Membership** (`jmem`), and the glue of `TermGlueObjSpec` at function `gObj`. The entry is
function `b`; its input is `tmRecIn ℓ σH σN X Y = [ℓ, gens H, gens N, X, Y]`.

**The program**, following the proof of Theorem A.20:

* `ℓ = 0` (`tmRiBaseE`): "the action is trivial, and equality of the multisets decides". The
  program compares the multisets by counts (`tmRi_ms_eq_iff`): `|X| = |Y|` and every entry of `X`
  has as many equal entries in `X` as in `Y`. Equality of two objects is the object test with the
  trivial group. The answer is `H` (`[1, gens H]`) or empty.
* `ℓ + 1` (`tmRiStepE`):
  1. `A = relDerived H N ℓ`, by `ℓ` steps `D ↦ ⟨[D, D], N⟩` (**DerivedSubgroup**, then the
     generators of `N` appended, cut to `n²` generators by **Membership**, `tmRiDerE`).
  2. The pieces of `X` and of `Y` (`tmRiPcsE`, `tmRiPcsStepE`): for each first position of an
     `A`-orbit, the entries in that orbit (`tmRiPcs_eq`). The orbit test of `L h` and `L h'` is
     the object test (`tmRiTestE`): one **SolvableCosetIntersection** call `A x ∩ h⁻¹ L h` with
     `x = h'⁻¹ h` (`tmRi_act_eq_iff`); different colors are never in one orbit.
  3. The table of pairwise transporters `Iso_H(S, T)` for all pieces `S, T` of both sides
     (`tmRiRowE`, `tmRiPairE`, `tmRiYE`): fix `x` = the first entry of `T`; for every `y ∈ S`, the
     object test with `H` gives a point transporter `τ_y` (`x^{τ_y} = y`) and the generators of
     `H_x`; one more **SolvableCosetIntersection** call gives `A ∩ H_x`; the recursive call on
     `(ℓ, H_x, A ∩ H_x, S^{τ_y⁻¹}, T)` gives `Iso_{H_x}(S^{τ_y⁻¹}, T)`, and the union of the
     `τ_y⁻¹ Iso_{H_x}(S^{τ_y⁻¹}, T)` is `Iso_H(S, T)` (`tmRi_pair_eq`). The union is formed by
     `GI.Lang.combine` and cut to `n²` generators by the coset normal form.
  4. The profiles (`tmRiProfE`): for the piece `S` at position `j`, the first position `r`
     with `Iso_H(P_r, S) ≠ ∅` is the color, the group is `A ⊔ Aut_H(P_r)` (the generators of `A`
     and of the answer for `(P_r, P_r)`, cut by Membership) and the representative is the one of
     the answer for `(P_r, S)` (`tmRec_prof_coset`).
  5. The recursive call on `(ℓ, H, A, Ŷ, X̂)` gives `Iso_H(Ŷ, X̂) = v Aut_H(X̂)`. If it is empty,
     the answer is empty (`tmRi_prof_empty`); otherwise the glue `gObj` is called with
     `B = Aut_H(X̂)` and `τ = v⁻¹`, so that `Iso_H(X̂, Ŷ) = B τ` (`tmRi_glue_pre`).

**Layout** (offsets from `b`): own functions `0`–`16`; modules: compose `17`, inverse `21`,
the map of conjugation `33`, `mkGroup` `36`, the Membership reduction `43`, append `48`, the
filter `51` and find `54` of the orbit test, the count test `57`, the loop of the pieces `60`, the
loop of the derived series `63`, the maps of rows `66`, pairs `69`, points `72`, shifts `75`,
profiles `78`, the find of a column `81`, range `84`, the combination `87`, the coset normal
form `90`. In all `96` functions (`length_tmRiFuns`).
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val SolvableCosetIntersection DerivedSubgroup Membership)

/-! ### The functions -/

/-- `0`, the entry, on `[ℓ, gens H, gens N, X, Y]`. -/
def tmRiMainE (b : ℕ) : Expr := .ite (arg 0) (.call (b + 2) (.var 0)) (.call (b + 1) (.var 0))

/-- `1`, the case `ℓ = 0`. Environment `[a, gens 1]`. -/
def tmRiBaseE (b : ℕ) : Expr :=
  .letE (mk2 (.get (arg 1) (.nat 0)) (mk1 (.get (.get (arg 1) (.nat 1)) (.nat 0))))
    (.ite (.arith .eq (.length (arg 3)) (.length (arg 4)))
      (.ite (.call (b + 57) (mk2 (mk3 (.var 1) (arg 3) (arg 4)) (arg 3)))
        (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0)) (arg 1))
        .nil)
      .nil)

/-- `2`, the case `ℓ + 1`. Environment `[a, ℓ', gens A, PX, PY, P, table, X̂, Ŷ, answer]`. -/
def tmRiStepE (b gObj : ℕ) : Expr :=
  .letE (.arith .sub (arg 0) (.nat 1))
  (.letE (.call (b + 63) (mk3 (mk2 (arg 1) (arg 2)) (.var 1) (arg 1)))
  (.letE (.call (b + 6) (mk2 (.var 2) (arg 3)))
  (.letE (.call (b + 6) (mk2 (.var 2) (arg 4)))
  (.letE (.call (b + 48) (mk2 (.var 3) (.var 4)))
  (.letE (.call (b + 66) (mk2 (mk4 (.var 1) (arg 1) (.var 2) (.var 5)) (.var 5)))
  (.letE (.call (b + 78) (mk2 (mk3 (.var 2) (.var 6) (.nat 0)) (.call (b + 84) (.length (.var 3)))))
  (.letE (.call (b + 78) (mk2 (mk3 (.var 2) (.var 6) (.length (.var 3)))
      (.call (b + 84) (.length (.var 4)))))
  (.letE (.call b (Expr.mkList [.var 1, arg 1, .var 2, .var 8, .var 7]))
    (.ite (.length (.var 9))
      (.call gObj (Expr.mkList [arg 1, arg 2, .var 2, arg 3, arg 4, .get (.var 9) (.nat 1),
        .call (b + 21) (.get (.var 9) (.nat 0))]))
      .nil)))))))))

/-- `3`, the orbit test as a predicate, on `[[gens G, o], z]`. -/
def tmRiObjP (b : ℕ) : Expr :=
  .ite (.isNat (.call (b + 5) (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))))
    (.nat 0) (.nat 1)

/-- `4`, the count test of the case `ℓ = 0`, on `[[gens 1, X, Y], x]`. -/
def tmRiCntP (b : ℕ) : Expr :=
  .arith .eq
    (.length (.call (b + 51) (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1)))))
    (.length (.call (b + 51) (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 2)))))

/-- `5`, the object test on `[gens G, [c, gens L, h], [c', gens L', h']]`: `0` if the colors
differ, otherwise the coset intersection `G (h'⁻¹ h) ∩ h⁻¹ L h`. Environment
`[a, h⁻¹, h'⁻¹, gens (h⁻¹ L h), h'⁻¹ h]`. -/
def tmRiTestE (b jsci : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 1) (.nat 0)) (.get (arg 2) (.nat 0)))
    (.letE (.call (b + 21) (.get (arg 1) (.nat 2)))
    (.letE (.call (b + 21) (.get (arg 2) (.nat 2)))
    (.letE (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call (b + 33) (mk2 (mk2 (.var 1) (.get (arg 1) (.nat 2)))
          (.get (.get (arg 1) (.nat 1)) (.nat 1)))))
    (.letE (.call (b + 17) (mk2 (.var 2) (.get (arg 1) (.nat 2))))
      (.prim jsci (mk3 (arg 0) (.var 3) (.var 4)))))))
    (.nat 0)

/-- `6`, the pieces of a list, on `[gens A, Z]`. -/
def tmRiPcsE (b : ℕ) : Expr := .call (b + 60) (mk3 (.var 0) (.length (arg 1)) .nil)

/-- `7`, one step of the pieces, on `[[gens A, Z], i, acc]`. Environment `[a, Z_i, [gens A, Z_i]]`. -/
def tmRiPcsStepE (b : ℕ) : Expr :=
  .letE (.get (.get (arg 0) (.nat 1)) (arg 1))
  (.letE (mk2 (.get (arg 0) (.nat 0)) (.var 1))
    (.ite (.arith .eq (.call (b + 54) (mk2 (.var 2) (.get (arg 0) (.nat 1)))) (arg 1))
      (.snoc (arg 2) (.call (b + 51) (mk2 (.var 2) (.get (arg 0) (.nat 1)))))
      (arg 2)))

/-- `8`, one step of the derived series, on `[[gens H, gens N], i, gens D]`:
`gens ⟨N, [D, D]⟩`, cut to `n²` generators. -/
def tmRiDerE (b jder : ℕ) : Expr :=
  .letE (.prim jder (arg 2))
    (.call (b + 43) (mk2 (.get (arg 2) (.nat 0))
      (.call (b + 48) (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 1)) (.var 1)))))

/-- `9`, one row of the table, on `[[ℓ', gens H, gens A, P], S]`: the answers for `(S, T)`, `T ∈ P`. -/
def tmRiRowE (b : ℕ) : Expr := .call (b + 69) (mk2 (.var 0) (.get (arg 0) (.nat 3)))

/-- `10`, one entry of the table, on `[[c, S], T]`: the pieces `τ_y⁻¹ Iso_{H_x}(S^{τ_y⁻¹}, T)`,
their combination and its normal form. -/
def tmRiPairE (b : ℕ) : Expr :=
  .letE (.call (b + 72) (mk2 (.var 0) (.get (arg 0) (.nat 1))))
  (.letE (.call (b + 87) (mk3 (.nat 0) (.var 1) .nil))
    (.call (b + 90) (.var 2)))

/-- The context `c = [ℓ', gens H, gens A, P]` in the argument `[[[c, S], T], y]` of `tmRiYE`. -/
def tmRiYc : Expr := .get (.get (arg 0) (.nat 0)) (.nat 0)
/-- The source piece `S`. -/
def tmRiYS : Expr := .get (.get (arg 0) (.nat 0)) (.nat 1)
/-- The target piece `T`. -/
def tmRiYT : Expr := .get (arg 0) (.nat 1)
/-- `gens H`. -/
def tmRiYH : Expr := .get tmRiYc (.nat 1)

/-- `11`, one point `y ∈ S`, on `[[[c, S], T], y]`: `[τ_y⁻¹, answer]`, or `[1, []]` when no
element of `H` carries `x = T_0` to `y`. Environment
`[a, test, τ_y, τ_y⁻¹, gens H_x, A ∩ H_x, gens (A ∩ H_x), S^{τ_y⁻¹}, answer]`. -/
def tmRiYE (b jsci : ℕ) : Expr :=
  .letE (.call (b + 5) (mk3 tmRiYH (.get tmRiYT (.nat 0)) (arg 1)))
    (.ite (.isNat (.var 1))
      (mk2 (.get (.get tmRiYH (.nat 1)) (.nat 0)) .nil)
      (.letE (.call (b + 17) (mk2 (.get (.var 1) (.nat 0))
          (.call (b + 17) (mk2 (.call (b + 21) (.get (.get tmRiYT (.nat 0)) (.nat 2)))
            (.get (arg 1) (.nat 2))))))
      (.letE (.call (b + 21) (.var 2))
      (.letE (.call (b + 36) (mk2 (.get tmRiYH (.nat 0)) (.get (.var 1) (.nat 1))))
      (.letE (.prim jsci (mk3 (.get tmRiYc (.nat 2)) (.var 4) (.get (.get tmRiYH (.nat 1)) (.nat 0))))
      (.letE (.call (b + 36) (mk2 (.get tmRiYH (.nat 0)) (.get (.var 5) (.nat 1))))
      (.letE (.call (b + 75) (mk2 (.var 3) tmRiYS))
      (.letE (.call b (Expr.mkList [.get tmRiYc (.nat 0), .var 4, .var 6, .var 7, tmRiYT]))
        (mk2 (.var 3) (.var 8))))))))))

/-- `12`, the shift of an object, on `[τ, [c, gens L, h]]`: `[c, gens L, h τ]`. -/
def tmRiShE (b : ℕ) : Expr :=
  mk3 (.get (arg 1) (.nat 0)) (.get (arg 1) (.nat 1))
    (.call (b + 17) (mk2 (.get (arg 1) (.nat 2)) (arg 0)))

/-- `13`, one profile, on `[[gens A, table, o], i]`, for the piece at `j = o + i`:
`[r, gens (A ⊔ Aut_H(P_r)), representative of the answer for (P_r, P_j)]`. Environment
`[a, j, r, answer (P_r, P_r), gens (A ⊔ Aut_H(P_r))]`. -/
def tmRiProfE (b : ℕ) : Expr :=
  .letE (.arith .add (.get (arg 0) (.nat 2)) (arg 1))
  (.letE (.call (b + 81) (mk2 (.var 1) (.get (arg 0) (.nat 1))))
  (.letE (.get (.get (.get (arg 0) (.nat 1)) (.var 2)) (.var 2))
  (.letE (.call (b + 43) (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.call (b + 48) (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 1))
        (.get (.get (.var 3) (.nat 1)) (.nat 1))))))
    (mk3 (.var 2) (.var 4)
      (.get (.get (.get (.get (arg 0) (.nat 1)) (.var 2)) (.var 1)) (.nat 0))))))

/-- `14`, the column test, on `[j, row]`: whether entry `j` of the row is nonempty. -/
def tmRiColP : Expr := .ite (.length (.get (arg 1) (arg 0))) (.nat 1) (.nat 0)

/-- The own functions `0`–`16`. -/
def tmRiOwn (b jsci jder gObj : ℕ) : List Expr :=
  [tmRiMainE b, tmRiBaseE b, tmRiStepE b gObj, tmRiObjP b, tmRiCntP b, tmRiTestE b jsci,
    tmRiPcsE b, tmRiPcsStepE b, tmRiDerE b jder, tmRiRowE b, tmRiPairE b, tmRiYE b jsci,
    tmRiShE b, tmRiProfE b, tmRiColP, supConjF (b + 17), combStep (b + 17) (b + 21) (b + 48)]

/-- **The code of the recursion of Theorem A.20** at base `b`. -/
def tmRiFuns (b jsci jder jmem gObj : ℕ) : List Expr :=
  tmRiOwn b jsci jder gObj ++ (composeFuns (b + 17) ++ (invFuns (b + 21) ++
  (mapFuns (b + 33) (b + 15) ++ (mkGroupFuns (b + 36) ++ (reduceFuns (b + 43) jmem ++
  (appendFuns (b + 48) ++ (filterFuns (b + 51) (b + 3) ++ (findFuns (b + 54) (b + 3) ++
  (allFuns (b + 57) (b + 4) ++ (iterFuns (b + 60) (b + 7) ++ (iterFuns (b + 63) (b + 8) ++
  (mapFuns (b + 66) (b + 9) ++ (mapFuns (b + 69) (b + 10) ++ (mapFuns (b + 72) (b + 11) ++
  (mapFuns (b + 75) (b + 12) ++ (mapFuns (b + 78) (b + 13) ++ (findFuns (b + 81) (b + 14) ++
  (rangeFuns (b + 84) ++ (foldlFuns (b + 87) (b + 16) ++ cosetNFFuns (b + 90) jmem)))))))))))))))))))

theorem length_tmRiFuns (b jsci jder jmem gObj : ℕ) :
    (tmRiFuns b jsci jder jmem gObj).length = 96 := rfl

/-- Splitting a placement, with the index of the second part given. -/
theorem tmRi_hasAt_right {P : Program} {b b' : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

/-! ### The layout -/

/-- **Where the recursion sits**: its code at `b` and the three cited primitives. -/
structure TmRiAt (P : Program) (b jsci jder jmem gObj : ℕ) (hsci : SolvableCosetIntersection)
    (hder : DerivedSubgroup) (hmem : Membership) : Prop where
  funs : P.HasAt b (tmRiFuns b jsci jder jmem gObj)
  sci : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci)
  der : P.prims[jder]? = some (derivedSubgroupPrim hder)
  mem : P.prims[jmem]? = some (membershipPrim hmem)

namespace TmRiAt

variable {P : Program} {b jsci jder jmem gObj : ℕ} {hsci : SolvableCosetIntersection}
  {hder : DerivedSubgroup} {hmem : Membership} (h : TmRiAt P b jsci jder jmem gObj hsci hder hmem)
include h

theorem own (j : ℕ) (hj : j < (tmRiOwn b jsci jder gObj).length) :
    P.funs[b + j]? = some (tmRiOwn b jsci jder gObj)[j] := h.funs.left j hj

theorem main : P.funs[b]? = some (tmRiMainE b) := by simpa [tmRiOwn] using h.own 0 (by simp [tmRiOwn])
theorem base : P.funs[b + 1]? = some (tmRiBaseE b) := by simpa [tmRiOwn] using h.own 1 (by simp [tmRiOwn])
theorem step : P.funs[b + 2]? = some (tmRiStepE b gObj) := by
  simpa [tmRiOwn] using h.own 2 (by simp [tmRiOwn])
theorem objP : P.funs[b + 3]? = some (tmRiObjP b) := by simpa [tmRiOwn] using h.own 3 (by simp [tmRiOwn])
theorem cntP : P.funs[b + 4]? = some (tmRiCntP b) := by simpa [tmRiOwn] using h.own 4 (by simp [tmRiOwn])
theorem test : P.funs[b + 5]? = some (tmRiTestE b jsci) := by
  simpa [tmRiOwn] using h.own 5 (by simp [tmRiOwn])
theorem pcs : P.funs[b + 6]? = some (tmRiPcsE b) := by simpa [tmRiOwn] using h.own 6 (by simp [tmRiOwn])
theorem pcsStep : P.funs[b + 7]? = some (tmRiPcsStepE b) := by
  simpa [tmRiOwn] using h.own 7 (by simp [tmRiOwn])
theorem derStep : P.funs[b + 8]? = some (tmRiDerE b jder) := by
  simpa [tmRiOwn] using h.own 8 (by simp [tmRiOwn])
theorem row : P.funs[b + 9]? = some (tmRiRowE b) := by simpa [tmRiOwn] using h.own 9 (by simp [tmRiOwn])
theorem pair : P.funs[b + 10]? = some (tmRiPairE b) := by
  simpa [tmRiOwn] using h.own 10 (by simp [tmRiOwn])
theorem y : P.funs[b + 11]? = some (tmRiYE b jsci) := by
  simpa [tmRiOwn] using h.own 11 (by simp [tmRiOwn])
theorem sh : P.funs[b + 12]? = some (tmRiShE b) := by simpa [tmRiOwn] using h.own 12 (by simp [tmRiOwn])
theorem prof : P.funs[b + 13]? = some (tmRiProfE b) := by
  simpa [tmRiOwn] using h.own 13 (by simp [tmRiOwn])
theorem colP : P.funs[b + 14]? = some tmRiColP := by simpa [tmRiOwn] using h.own 14 (by simp [tmRiOwn])
theorem cj : P.funs[b + 15]? = some (supConjF (b + 17)) := by
  simpa [tmRiOwn] using h.own 15 (by simp [tmRiOwn])
theorem combS : P.funs[b + 16]? = some (combStep (b + 17) (b + 21) (b + 48)) := by
  simpa [tmRiOwn] using h.own 16 (by simp [tmRiOwn])

/-- The placement of the modules. -/
theorem mods :
    P.HasAt (b + 17) (composeFuns (b + 17)) ∧
    P.HasAt (b + 21) (invFuns (b + 21)) ∧
    P.HasAt (b + 33) (mapFuns (b + 33) (b + 15)) ∧
    P.HasAt (b + 36) (mkGroupFuns (b + 36)) ∧
    P.HasAt (b + 43) (reduceFuns (b + 43) jmem) ∧
    P.HasAt (b + 48) (appendFuns (b + 48)) ∧
    P.HasAt (b + 51) (filterFuns (b + 51) (b + 3)) ∧
    P.HasAt (b + 54) (findFuns (b + 54) (b + 3)) ∧
    P.HasAt (b + 57) (allFuns (b + 57) (b + 4)) ∧
    P.HasAt (b + 60) (iterFuns (b + 60) (b + 7)) ∧
    P.HasAt (b + 63) (iterFuns (b + 63) (b + 8)) ∧
    P.HasAt (b + 66) (mapFuns (b + 66) (b + 9)) ∧
    P.HasAt (b + 69) (mapFuns (b + 69) (b + 10)) ∧
    P.HasAt (b + 72) (mapFuns (b + 72) (b + 11)) ∧
    P.HasAt (b + 75) (mapFuns (b + 75) (b + 12)) ∧
    P.HasAt (b + 78) (mapFuns (b + 78) (b + 13)) ∧
    P.HasAt (b + 81) (findFuns (b + 81) (b + 14)) ∧
    P.HasAt (b + 84) (rangeFuns (b + 84)) ∧
    P.HasAt (b + 87) (foldlFuns (b + 87) (b + 16)) ∧
    P.HasAt (b + 90) (cosetNFFuns (b + 90) jmem) := by
  have h0 := tmRi_hasAt_right h.funs (b' := b + 17) rfl
  have h1 := tmRi_hasAt_right h0 (b' := b + 21) rfl
  have h2 := tmRi_hasAt_right h1 (b' := b + 33) rfl
  have h3 := tmRi_hasAt_right h2 (b' := b + 36) rfl
  have h4 := tmRi_hasAt_right h3 (b' := b + 43) rfl
  have h5 := tmRi_hasAt_right h4 (b' := b + 48) rfl
  have h6 := tmRi_hasAt_right h5 (b' := b + 51) rfl
  have h7 := tmRi_hasAt_right h6 (b' := b + 54) rfl
  have h8 := tmRi_hasAt_right h7 (b' := b + 57) rfl
  have h9 := tmRi_hasAt_right h8 (b' := b + 60) rfl
  have h10 := tmRi_hasAt_right h9 (b' := b + 63) rfl
  have h11 := tmRi_hasAt_right h10 (b' := b + 66) rfl
  have h12 := tmRi_hasAt_right h11 (b' := b + 69) rfl
  have h13 := tmRi_hasAt_right h12 (b' := b + 72) rfl
  have h14 := tmRi_hasAt_right h13 (b' := b + 75) rfl
  have h15 := tmRi_hasAt_right h14 (b' := b + 78) rfl
  have h16 := tmRi_hasAt_right h15 (b' := b + 81) rfl
  have h17 := tmRi_hasAt_right h16 (b' := b + 84) rfl
  have h18 := tmRi_hasAt_right h17 (b' := b + 87) rfl
  have h19 := tmRi_hasAt_right h18 (b' := b + 90) rfl
  exact ⟨h0.left, h1.left, h2.left, h3.left, h4.left, h5.left, h6.left, h7.left, h8.left, h9.left, h10.left, h11.left, h12.left, h13.left, h14.left, h15.left, h16.left, h17.left, h18.left, h19⟩

theorem comp : P.HasAt (b + 17) (composeFuns (b + 17)) := h.mods.1
theorem inv : P.HasAt (b + 21) (invFuns (b + 21)) := h.mods.2.1
theorem mapConj : P.HasAt (b + 33) (mapFuns (b + 33) (b + 15)) := h.mods.2.2.1
theorem mg : P.HasAt (b + 36) (mkGroupFuns (b + 36)) := h.mods.2.2.2.1
theorem red : P.HasAt (b + 43) (reduceFuns (b + 43) jmem) := h.mods.2.2.2.2.1
theorem app : P.HasAt (b + 48) (appendFuns (b + 48)) := h.mods.2.2.2.2.2.1
theorem filt : P.HasAt (b + 51) (filterFuns (b + 51) (b + 3)) := h.mods.2.2.2.2.2.2.1
theorem find : P.HasAt (b + 54) (findFuns (b + 54) (b + 3)) := h.mods.2.2.2.2.2.2.2.1
theorem all : P.HasAt (b + 57) (allFuns (b + 57) (b + 4)) := h.mods.2.2.2.2.2.2.2.2.1
theorem iterPcs : P.HasAt (b + 60) (iterFuns (b + 60) (b + 7)) := h.mods.2.2.2.2.2.2.2.2.2.1
theorem iterDer : P.HasAt (b + 63) (iterFuns (b + 63) (b + 8)) := h.mods.2.2.2.2.2.2.2.2.2.2.1
theorem mapRow : P.HasAt (b + 66) (mapFuns (b + 66) (b + 9)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.1
theorem mapPair : P.HasAt (b + 69) (mapFuns (b + 69) (b + 10)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem mapY : P.HasAt (b + 72) (mapFuns (b + 72) (b + 11)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem mapSh : P.HasAt (b + 75) (mapFuns (b + 75) (b + 12)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem mapProf : P.HasAt (b + 78) (mapFuns (b + 78) (b + 13)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem findC : P.HasAt (b + 81) (findFuns (b + 81) (b + 14)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem range : P.HasAt (b + 84) (rangeFuns (b + 84)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem comb : P.HasAt (b + 87) (foldlFuns (b + 87) (b + 16)) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cnf : P.HasAt (b + 90) (cosetNFFuns (b + 90) jmem) := h.mods.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end TmRiAt

end GI.Impl
