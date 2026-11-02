import Workspace.Impl.GenCosets
import Workspace.Impl.GenCls
import Workspace.Impl.DomRestrict
import Workspace.Impl.NIntInter
import Workspace.Lang.Lib.Schreier
import Workspace.Lang.Prims.Blocks

/-!
# The program of the solvable coset intersection

Source: [LM] = Luks–Miyazaki, DMTCS 13:4 (2011), Proposition 3.9, pp. 71–72. The mathematics is
in `Workspace/Proved/SCosMath.lean` (the case lemmas), `SCosPalfy.lean` (the number of cosets)
and `SCosCount.lean` (the running time).

`N = n + n`. A pair `(a, b)` of permutations of `Fin n` is the permutation `a ⊕ b` of `Fin N`
(`nintSum`). A **problem** is the value `[gv, xv, ind]`: `gv` a group value of a group of pairs
`𝒢`, `xv = encPerm x` for a pair `x`, and `ind` the indicator of a set `Φ` of points of the first
copy of `Fin n`. The **answer** is `[]` or a coset value `[z, lv]` of the subcoset `C(x 𝒢, Φ)`
(`scosC`).

The functions (base 0):

* `0` `solveF`: `Φ = ∅` gives `[xv, gv]`; otherwise `nodeF`.
* `1` `nodeF`: the orbit `O` of the least point `α` of `Φ` (orbit labels, the indicator of the
  points with the label of `α`); `O ≠ Φ` (fewer points) gives `splitF`, else `transF`.
* `2` `splitF`: solve on `O`; `[]` stays `[]`; else `[z, lv]`, then solve `[lv, z, Φ \ O]`.
* `3` `transF`: `|Φ| = 1` gives `baseF`, else `bigF`.
* `4` `baseF`: `Φ = {α}`. The point `τ = x⁻¹ (n + x α)` (that is `n + x₂⁻¹ x₁ α`), the
  Schreier transversal of `n + α`; if `τ` is in the orbit, with `t (n + α) = τ`, the answer
  `[x t, 𝒢_{n+α}]`, else `[]`.
* `5` `bigF`: the restriction of `𝒢` to `Φ`, a minimal block system of it (`MinimalBlocks`),
  pulled back to `Fin N` (`labN`, off `Φ` the label `|Φ|`), its representatives (`clsFuns`), the
  kernel `K` (`kerFuns`, `Preimage`), the coset representatives `t` of `K` (the orbit of `labN`,
  `cosetsFuns`, with bound `B = (N + 1)^c`), the children `[kv, x t, ind]` (`childF`), pasted by
  `pasteF`.
* `6` `childF`, `7` `pasteF`, `8` `goodTestF`, `9` `extraStepF`, `10` `subStepF`,
  `11` `ptTestF`: helpers.
* `12` `topF`: the entry, on the task input `[encGroup gs, encGroup hs, encPerm x]`. The group
  `G × H` by the pairs `(g, 1)`, `(1, h)`, normalized by a pointwise stabilizer of no points; the
  pair `(x⁻¹, 1)`; `Φ` = the first copy. From the answer `[z, lv]`: `y = (z₁)⁻¹` and the first
  coordinates of the generators of `lv`, cut to at most `n²` by the pointwise-stabilizer task.
* `13` `pairG1F`, `14` `pairH1F`, `15` `ltStepF`: helpers of `topF`.
* `16`–`267`: library functions (see `scosFuns`).

Primitives: `0` pointwise stabilizer, `1` preimage, `2` minimal blocks.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv

/-- A list of five values. -/
def scosMk5 (a b c d e : Expr) : Expr := .snoc (mk4 a b c d) e

/-- `e ^ c`, as a product. -/
def scosPowE : ℕ → Expr → Expr
  | 0, _ => .nat 1
  | c + 1, e => .arith .mul (scosPowE c e) e

/-! ### The functions -/

/-- `0`: on `[gv, xv, ind]`. -/
def scosSolveF : Expr :=
  .ite (.call 24 (mk2 (.nat 1) (arg 2))) (.call 1 (.var 0)) (mk2 (arg 1) (arg 0))

/-- `1`: on `[gv, xv, ind]`, `Φ ≠ ∅`. -/
def scosNodeF : Expr :=
  .letE (.call 37 (arg 0))
  (.letE (.call 29 (mk2 (.nat 1) (arg 2)))
  (.letE (.call 33 (mk2 (.get (.var 1) (.var 2)) (.var 1)))
  (.ite (.arith .eq (.call 24 (mk2 (.nat 1) (.var 3))) (.call 24 (mk2 (.nat 1) (arg 2))))
    (.call 3 (.var 0))
    (.call 2 (mk4 (arg 0) (arg 1) (arg 2) (.var 3))))))

/-- `2`: on `[gv, xv, ind, oind]`. -/
def scosSplitF : Expr :=
  .letE (.call 0 (mk3 (arg 0) (arg 1) (arg 3)))
  (.ite (.length (.var 1))
    (.call 0 (mk3 (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 0))
      (.call 69 (mk2 (mk2 (arg 2) (arg 3)) (.call 72 (.length (arg 2)))))))
    (.var 1))

/-- `3`: on `[gv, xv, ind]`, `𝒢` transitive on `Φ`. -/
def scosTransF : Expr :=
  .ite (.arith .eq (.call 24 (mk2 (.nat 1) (arg 2))) (.nat 1)) (.call 4 (.var 0)) (.call 5 (.var 0))

/-- `4`: on `[gv, xv, ind]`, `Φ = {α}`. The environment: `α`, `n`, `n + α`, `τ`, the
transversal, the index of `τ` in it. -/
def scosBaseF : Expr :=
  .letE (.call 29 (mk2 (.nat 1) (arg 2)))
  (.letE (.arith .div (.length (arg 1)) (.nat 2))
  (.letE (.arith .add (.var 2) (.var 1))
  (.letE (.get (.call 75 (arg 1)) (.arith .add (.var 2) (.get (arg 1) (.var 1))))
  (.letE (.call 91 (scosMk5 (.nat 0) (.get (arg 0) (.nat 1)) (mk1 (.var 3)) (.length (arg 1))
      (.length (arg 1))))
  (.letE (.call 114 (mk2 (.var 4) (.var 5)))
  (.ite (.arith .lt (.var 6) (.length (.var 5)))
    (mk2 (.call 87 (mk2 (arg 1) (.get (.get (.var 5) (.var 6)) (.nat 1))))
      (.call 117 (mk2 (arg 0) (mk1 (.var 3)))))
    .nil))))))

/-- `5`: on `[gv, xv, ind]`, `𝒢` transitive on `Φ`, `|Φ| ≥ 2`. The environment: the positions
`P` of `Φ`, the table of positions, the restricted generators, the restricted group, the
minimal block labels, `labN`, the representatives, the kernel, the coset pairs. -/
def scosBigF (c : ℕ) : Expr :=
  .letE (.call 125 (arg 2))
  (.letE (.call 133 (mk2 (.var 1) (.length (arg 2))))
  (.letE (.call 147 (mk2 (mk2 (.var 1) (.var 2)) (.get (arg 0) (.nat 1))))
  (.letE (.call 150 (mk2 (.length (.var 1)) (.var 3)))
  (.letE (.prim 2 (.var 4))
  (.letE (.call 157 (mk2 (.snoc (.var 5) (.length (.var 1))) (.var 2)))
  (.letE (.get (.call 161 (mk2 (.var 6) (arg 2))) (.nat 2))
  (.letE (.call 185 (mk2 (arg 0) (.var 7)))
  (.letE (.call 206 (scosMk5 (.nat 0) (.get (arg 0) (.nat 1)) (.var 6)
      (scosPowE c (.arith .add (.length (arg 1)) (.nat 1))) (.length (arg 1))))
  (.call 7 (.call 241 (mk2 (mk3 (.var 8) (arg 1) (arg 2)) (.var 9))))))))))))

/-- `6`: on `[[kv, xv, ind], [f, t]]`, the child `[kv, x t, ind]`, solved. -/
def scosChildF : Expr :=
  .call 0 (mk3 (.get (arg 0) (.nat 0))
    (.call 87 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1)))) (.get (arg 0) (.nat 2)))

/-- `7`: on the list of the answers of the children. The environment: the nonempty answers,
the first one `[z₁, lv₁]`, `z₁⁻¹`, the list of the `z₁⁻¹ zⱼ`, the group value of `lv₁` with them. -/
def scosPasteF : Expr :=
  .letE (.call 244 (mk2 (.nat 0) (.var 0)))
  (.ite (.length (.var 1))
    (.letE (.get (.var 1) (.nat 0))
    (.letE (.call 75 (.get (.var 2) (.nat 0)))
    (.letE (.call 247 (mk2 (.var 3) (.var 1)))
    (.letE (.call 150 (mk2 (.length (.var 3))
      (.call 250 (mk2 (.get (.get (.var 2) (.nat 1)) (.nat 1)) (.var 4)))))
    (mk2 (.get (.var 2) (.nat 0)) (.call 117 (mk2 (.var 5) .nil)))))))
    .nil)

/-- `8`: on `[c, a]`, whether `a` is a nonempty list. -/
def scosGoodTestF : Expr := .arith .lt (.nat 0) (.length (arg 1))

/-- `9`: on `[z₁⁻¹, [z, lv]]`, `z₁⁻¹ z`. -/
def scosExtraStepF : Expr := .call 87 (mk2 (arg 0) (.get (arg 1) (.nat 0)))

/-- `10`: on `[[ind, oind], i]`, `ind[i] - oind[i]`. -/
def scosSubStepF : Expr :=
  .arith .sub (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (.get (arg 0) (.nat 1)) (arg 1))

/-- `11`: on `[τ, [[β], t]]`, whether `β = τ`. -/
def scosPtTestF : Expr := .arith .eq (.get (.get (arg 1) (.nat 0)) (.nat 0)) (arg 0)

/-- `12`: the entry, on `[encGroup gs, encGroup hs, encPerm x]`. The environment: `n`,
`encPerm 1`, the generators `(g, 1)`, `(1, h)`, the normalized group value, `(x⁻¹, 1)`, the
answer, `z₁`. -/
def scosTopF : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.call 72 (.var 1))
  (.letE (.call 250 (mk2 (.call 259 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 0) (.nat 1))))
      (.call 262 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 1) (.nat 1))))))
  (.letE (.call 117 (mk2 (mk2 (.arith .add (.var 1) (.var 1)) (.var 3)) .nil))
  (.letE (.call 16 (mk3 (.call 75 (arg 2)) (.var 2) (.var 1)))
  (.letE (.call 0 (mk3 (.var 4) (.var 5)
      (.call 265 (mk2 (.var 1) (.call 72 (.arith .add (.var 1) (.var 1)))))))
  (.ite (.length (.var 6))
    (.letE (.call 253 (mk2 (.var 1) (.get (.var 6) (.nat 0))))
      (mk2 (.call 75 (.var 7))
        (.prim 0 (mk2 (mk2 (.var 1) (.call 256 (mk2 (.var 1)
          (.get (.get (.var 6) (.nat 1)) (.nat 1))))) .nil))))
    (.nat 0)))))))

/-- `13`: on `[[1, n], g]`, `g ⊕ 1`. -/
def scosPairG1F : Expr := .call 16 (mk3 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))

/-- `14`: on `[[1, n], h]`, `1 ⊕ h`. -/
def scosPairH1F : Expr := .call 16 (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1)))

/-- `15`: on `[n, i]`, whether `i < n`. -/
def scosLtStepF : Expr := .arith .lt (arg 1) (arg 0)

/-- The own functions `0`–`15`. -/
def scosOwnFuns (c : ℕ) : List Expr :=
  [scosSolveF, scosNodeF, scosSplitF, scosTransF, scosBaseF, scosBigF c, scosChildF, scosPasteF,
    scosGoodTestF, scosExtraStepF, scosSubStepF, scosPtTestF, scosTopF, scosPairG1F,
    scosPairH1F, scosLtStepF]

/-- **The functions of the program.** -/
def scosFuns (c : ℕ) : List Expr :=
  scosOwnFuns c ++ [shiftAppF 17 20] ++ appendFuns 17 ++ mapFuns 20 23 ++ [addKF] ++
    countFuns 24 ++ findEqFuns 29 ++ eqIndFuns 33 ++ orbitFuns 37 ++ mapFuns 69 10 ++
    rangeFuns 72 ++ invFuns 75 ++ composeFuns 87 ++ schreierFuns 91 ++ findFuns 114 11 ++
    pstabFuns 117 0 ++ domFuns 125 ++ mkGroupFuns 150 ++ gatherFuns 157 ++ clsFuns 161 ++
    kerFuns 185 1 ++ cosetsFuns 206 ++ mapFuns 241 6 ++ filterFuns 244 8 ++ mapFuns 247 9 ++
    appendFuns 250 ++ linTakeFuns 253 ++ mapFuns 256 253 ++ mapFuns 259 13 ++
    mapFuns 262 14 ++ mapFuns 265 15

/-- **The program**, with the pointwise stabilizer, the preimage and the minimal blocks as
primitives `0`, `1`, `2`. -/
noncomputable def scosProgram (c : ℕ) (hps : PointwiseStab) (hpre : Preimage)
    (hmb : MinimalBlocks) : Program :=
  ⟨scosFuns c, [pointwiseStabPrim hps, preimagePrim hpre, minimalBlocksPrim hmb]⟩

theorem length_scosFuns (c : ℕ) : (scosFuns c).length = 268 := by
  simp [scosFuns, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns,
    length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns,
    pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns,
    filterFuns, linTakeFuns, loopFuns, graphValFuns]

/-! ### Layout -/

section Layout

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- The whole function list sits at `0`. -/
theorem scos_hasAt : (scosProgram c hps hpre hmb).HasAt 0 (scosFuns c) := by
  simpa using Program.hasAt_append [] (scosFuns c) []
    [pointwiseStabPrim hps, preimagePrim hpre, minimalBlocksPrim hmb]

/-- The function list, unfolded. -/
theorem scos_all : (scosProgram c hps hpre hmb).HasAt 0 (scosOwnFuns c ++ [shiftAppF 17 20] ++
    appendFuns 17 ++ mapFuns 20 23 ++ [addKF] ++
    countFuns 24 ++ findEqFuns 29 ++ eqIndFuns 33 ++ orbitFuns 37 ++ mapFuns 69 10 ++
    rangeFuns 72 ++ invFuns 75 ++ composeFuns 87 ++ schreierFuns 91 ++ findFuns 114 11 ++
    pstabFuns 117 0 ++ domFuns 125 ++ mkGroupFuns 150 ++ gatherFuns 157 ++ clsFuns 161 ++
    kerFuns 185 1 ++ cosetsFuns 206 ++ mapFuns 241 6 ++ filterFuns 244 8 ++ mapFuns 247 9 ++
    appendFuns 250 ++ linTakeFuns 253 ++ mapFuns 256 253 ++ mapFuns 259 13 ++
    mapFuns 262 14 ++ mapFuns 265 15) := scos_hasAt

/-- `P` for short. -/
local notation "𝒫" => scosProgram c hps hpre hmb

theorem scos_own : (𝒫).HasAt 0 (scosOwnFuns c) := by
  have h := scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)
  exact h.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left
theorem scos_shift : (𝒫).funs[16]? = some (shiftAppF 17 20) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h.single
theorem scos_append1 : (𝒫).HasAt 17 (appendFuns 17) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_shiftMap : (𝒫).HasAt 20 (mapFuns 20 23) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_addK : (𝒫).funs[23]? = some (addKF) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h.single
theorem scos_count : (𝒫).HasAt 24 (countFuns 24) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_findEq : (𝒫).HasAt 29 (findEqFuns 29) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_eqInd : (𝒫).HasAt 33 (eqIndFuns 33) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_orbit : (𝒫).HasAt 37 (orbitFuns 37) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_subMap : (𝒫).HasAt 69 (mapFuns 69 10) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_range : (𝒫).HasAt 72 (rangeFuns 72) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_inv : (𝒫).HasAt 75 (invFuns 75) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_compose : (𝒫).HasAt 87 (composeFuns 87) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_schreier : (𝒫).HasAt 91 (schreierFuns 91) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_findPt : (𝒫).HasAt 114 (findFuns 114 11) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_pstab : (𝒫).HasAt 117 (pstabFuns 117 0) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_dom : (𝒫).HasAt 125 (domFuns 125) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_mkGroup : (𝒫).HasAt 150 (mkGroupFuns 150) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_gather : (𝒫).HasAt 157 (gatherFuns 157) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_cls : (𝒫).HasAt 161 (clsFuns 161) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_ker : (𝒫).HasAt 185 (kerFuns 185 1) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_cosets : (𝒫).HasAt 206 (cosetsFuns 206) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_childMap : (𝒫).HasAt 241 (mapFuns 241 6) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_filter : (𝒫).HasAt 244 (filterFuns 244 8) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_extraMap : (𝒫).HasAt 247 (mapFuns 247 9) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_append2 : (𝒫).HasAt 250 (appendFuns 250) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_take : (𝒫).HasAt 253 (linTakeFuns 253) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_takeMap : (𝒫).HasAt 256 (mapFuns 256 253) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_g1Map : (𝒫).HasAt 259 (mapFuns 259 13) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_h1Map : (𝒫).HasAt 262 (mapFuns 262 14) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).left.right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_ltMap : (𝒫).HasAt 265 (mapFuns 265 15) := by
  have h := (scos_all (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)).right
  simp only [List.length_append, List.length_cons, List.length_nil, scosOwnFuns, appendFuns, mapFuns, countFuns, findEqFuns, eqIndFuns, length_orbitFuns, rangeFuns, invFuns, composeFuns, schreierFuns, length_orbTFuns, findFuns, pstabFuns, length_domFuns, mkGroupFuns, gatherFuns, length_clsFuns, kerFuns, cosetsFuns, filterFuns, linTakeFuns, loopFuns, graphValFuns] at h
  exact h
theorem scos_solve : (𝒫).funs[0]? = some (scosSolveF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 0) (by simp [scosOwnFuns])
theorem scos_node : (𝒫).funs[1]? = some (scosNodeF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 1) (by simp [scosOwnFuns])
theorem scos_split : (𝒫).funs[2]? = some (scosSplitF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 2) (by simp [scosOwnFuns])
theorem scos_trans : (𝒫).funs[3]? = some (scosTransF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 3) (by simp [scosOwnFuns])
theorem scos_base : (𝒫).funs[4]? = some (scosBaseF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 4) (by simp [scosOwnFuns])
theorem scos_big : (𝒫).funs[5]? = some (scosBigF c) := by
  simpa [scosOwnFuns] using scos_own.get (j := 5) (by simp [scosOwnFuns])
theorem scos_child : (𝒫).funs[6]? = some (scosChildF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 6) (by simp [scosOwnFuns])
theorem scos_paste : (𝒫).funs[7]? = some (scosPasteF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 7) (by simp [scosOwnFuns])
theorem scos_goodTest : (𝒫).funs[8]? = some (scosGoodTestF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 8) (by simp [scosOwnFuns])
theorem scos_extraStep : (𝒫).funs[9]? = some (scosExtraStepF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 9) (by simp [scosOwnFuns])
theorem scos_subStep : (𝒫).funs[10]? = some (scosSubStepF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 10) (by simp [scosOwnFuns])
theorem scos_ptTest : (𝒫).funs[11]? = some (scosPtTestF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 11) (by simp [scosOwnFuns])
theorem scos_top : (𝒫).funs[12]? = some (scosTopF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 12) (by simp [scosOwnFuns])
theorem scos_pairG1 : (𝒫).funs[13]? = some (scosPairG1F) := by
  simpa [scosOwnFuns] using scos_own.get (j := 13) (by simp [scosOwnFuns])
theorem scos_pairH1 : (𝒫).funs[14]? = some (scosPairH1F) := by
  simpa [scosOwnFuns] using scos_own.get (j := 14) (by simp [scosOwnFuns])
theorem scos_ltStep : (𝒫).funs[15]? = some (scosLtStepF) := by
  simpa [scosOwnFuns] using scos_own.get (j := 15) (by simp [scosOwnFuns])
theorem scos_prim0 : (𝒫).prims[0]? = some (pointwiseStabPrim hps) := rfl
theorem scos_prim1 : (𝒫).prims[1]? = some (preimagePrim hpre) := rfl
theorem scos_prim2 : (𝒫).prims[2]? = some (minimalBlocksPrim hmb) := rfl

theorem scos_domAt : DomAt (𝒫) 125 := domAt_of_hasAt scos_dom

end Layout

end GI.Impl
