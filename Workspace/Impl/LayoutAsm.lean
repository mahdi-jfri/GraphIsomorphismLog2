import Workspace.Impl.Direct
import Workspace.Impl.Floor
import Workspace.Impl.RestSel
import Workspace.Impl.GiantSel
import Workspace.Impl.Cases
import Workspace.Assembly.Wrapper

/-!
# The concrete program of stage 2

This file builds one `GI.Lang` program that holds every step of the recursion that is
implemented, the three dispatchers, the selectors and the wrapper of Algorithm 1. The three
steps that are not implemented yet (the general dispatcher, the row step and the aggregation
round) are given as function lists `gen`, `row`, `agg`, placed at fixed bases.

## The function table

The table is `asmCore ++ pad ++ gen ++ pad ++ row ++ pad ++ agg`:

* `asmCore` (402 functions at `0`): the dispatchers of `Solve`, `Continue`, `GiantStep` at
  `0, 1, 2` (`asmF`), the single-function steps and helpers at `3, …, 13`, then the library
  modules (see `asmCore` for the bases), and the wrapper `wrapperFuns 347 0` at `347`;
* `gen` at `asmGenBase = 10⁶`, `row` at `asmRowBase = 2·10⁶`, `agg` at `asmAggBase = 3·10⁶`;
  each list must have at most `10⁶` functions (`asmProg_hasAt_gen`, …), and the gaps are
  filled with `.nil`.

## The primitive table

`[PointwiseStab, Membership, Preimage, NormalizedFactor] ++ extra`, at `0, 1, 2, 3`. The list
`extra` holds the cited primitives that the missing steps need, from index `4` on
(`asmProg_prim_extra`).

## The interface

`asmRest` is the concrete `Rest`: `solveK, solveD` from the direct and fresh steps
(`Rest.solveKOf`, `Rest.solveDOf`), `restSelB` from `RestSel`, `giantSelW = giantSelWStd`, and
the works `Wg, Wr, Wa` of the missing steps as parameters.

`asm_layoutOK`: the layout `asmLayout` meets `Layout.OK` for `asmRest.iface`, given the step
specifications of the three missing steps.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership)

set_option maxRecDepth 100000

/-! ### Indices -/

/-- The three recursive functions. -/
def asmF : Funs := ⟨0, 1, 2⟩

/-- The base of the general dispatcher. -/
def asmGenBase : ℕ := 1000000
/-- The base of the row step. -/
def asmRowBase : ℕ := 2000000
/-- The base of the aggregation round. -/
def asmAggBase : ℕ := 3000000
/-- The room for each of the three missing steps. -/
def asmSlot : ℕ := 1000000

/-- The first index of the extra primitives. -/
def asmPrimBase : ℕ := 4

/-! ### The core of the function table

Single functions:
`0` solve, `1` cont, `2` giant (dispatchers), `3` threshold, `4` floor, `5` orbit,
`6` rest of the `Continue` selector, `7` direct, `8` fresh, `9` prep, `10` color,
`11` orbit hierarchy, `12` coset enumeration, `13` color test.

Blocks: `14` solve selector (6), `20` cont selector (6), `26` giant selector (73), `99` size (5),
`104` reduce (8), `112` domain restriction (25), `137` append (3), `140` replicate (3),
`143` largest orbit (62), `205` count (5), `210` orbits (32), `242` enumeration (28),
`270` filter (3), `273` compose (4), `277` equality of lists (3), `280` coset normal form (6),
`286` range (3), `289` lift (31), `320` split (18), `338` gather (4), `342` max (5),
`347` wrapper (55). -/
noncomputable def asmCore : List Expr :=
  [modeBody 14 [7, 8],
    modeBody 20 [3, 5, 4, asmGenBase],
    modeBody 26 [asmRowBase, asmAggBase],
    thresholdBody asmF,
    floorBody asmF,
    orbitBody asmF 143 320 338 273,
    restSelBody 143 342 320,
    directBody 99 9 104 286 12 289,
    freshBody 9 asmF.cont 289,
    prepBody 104 112 10 11,
    colorBody (112 + 18) 137 (112 + 9),
    hierBody 140 143 205 210,
    cosetFinF P₀.N₀.factorial 242 270 280 137 286,
    colTestF 273 277] ++
  solveSelFuns 14 ++ contSelFuns 20 6 ++ giantSelFuns 26 2 ++ sizeFuns 99 ++ redFuns 104 0 ++
  domFuns 112 ++ appendFuns 137 ++ replicateFuns 140 ++ loFuns 143 ++ countFuns 205 ++
  orbitFuns 210 ++ enumFuns 242 ++ filterFuns 270 13 ++ composeFuns 273 ++ eqNatsFuns 277 ++
  cosetNFFuns 280 1 ++ rangeFuns 286 ++ liftFuns 289 112 2 3 ++ splitFuns 320 ++
  gatherFuns 338 ++ maxFuns 342 ++ wrapperFuns 347 0

theorem length_asmCore : asmCore.length = 402 := rfl

/-- A list padded with `.nil` to length `n`. -/
def asmPad (n : ℕ) (l : List Expr) : List Expr := l ++ List.replicate (n - l.length) .nil

theorem length_asmPad {n : ℕ} {l : List Expr} (h : l.length ≤ n) : (asmPad n l).length = n := by
  simp [asmPad]; omega

/-- **The program.** -/
noncomputable def asmProg (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (extra : List Prim) (gen row agg : List Expr) : Program where
  funs := asmPad asmSlot asmCore ++ asmPad asmSlot gen ++ asmPad asmSlot row ++ agg
  prims := [pointwiseStabPrim hst, membershipPrim hm, preimagePrim hpre,
    normalizedFactorPrim hfac] ++ extra

/-- **The layout** of the recursion in `asmProg`. -/
def asmLayout : Iface.Layout where
  F := asmF
  solveSel := 14
  direct := 7
  fresh := 8
  contSel := 20
  threshold := 3
  orbit := 5
  floor := 4
  general := asmGenBase
  giantSel := 26
  row := asmRowBase
  agg := asmAggBase

section Prog

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {extra : List Prim} {gen row agg : List Expr}

/-! ### Where the functions sit -/

theorem asmProg_hasAt_core :
    (asmProg hst hm hpre hfac extra gen row agg).HasAt 0 asmCore := by
  intro j hj
  have hj' : j < 402 := length_asmCore ▸ hj
  have hc : (asmPad asmSlot asmCore).length = asmSlot :=
    length_asmPad (by rw [length_asmCore]; decide)
  have hjs : j < (asmPad asmSlot asmCore).length := by rw [hc]; unfold asmSlot; omega
  simp only [asmProg, Nat.zero_add, List.append_assoc]
  rw [List.getElem?_append_left hjs, asmPad, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hj]

/-- The functions of the general dispatcher sit at `asmGenBase`. -/
theorem asmProg_hasAt_gen (h : gen.length ≤ asmSlot) :
    (asmProg hst hm hpre hfac extra gen row agg).HasAt asmGenBase gen := by
  intro j hj
  have hc : (asmPad asmSlot asmCore).length = asmSlot :=
    length_asmPad (by rw [length_asmCore]; decide)
  simp only [asmProg, List.append_assoc]
  rw [List.getElem?_append_right (by rw [hc]; unfold asmGenBase asmSlot; omega), hc,
    show asmGenBase + j - asmSlot = j by unfold asmGenBase asmSlot; omega,
    List.getElem?_append_left (by rw [length_asmPad h]; omega), asmPad,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- The functions of the row step sit at `asmRowBase`. -/
theorem asmProg_hasAt_row (hg : gen.length ≤ asmSlot) (h : row.length ≤ asmSlot) :
    (asmProg hst hm hpre hfac extra gen row agg).HasAt asmRowBase row := by
  intro j hj
  have hc : (asmPad asmSlot asmCore).length = asmSlot :=
    length_asmPad (by rw [length_asmCore]; decide)
  have hg' : (asmPad asmSlot gen).length = asmSlot := length_asmPad hg
  simp only [asmProg, List.append_assoc]
  rw [List.getElem?_append_right (by rw [hc]; unfold asmRowBase asmSlot; omega), hc,
    List.getElem?_append_right (by rw [hg']; unfold asmRowBase asmSlot; omega), hg',
    show asmRowBase + j - asmSlot - asmSlot = j by unfold asmRowBase asmSlot; omega,
    List.getElem?_append_left (by rw [length_asmPad h]; omega), asmPad,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- The functions of the aggregation round sit at `asmAggBase`. -/
theorem asmProg_hasAt_agg (hg : gen.length ≤ asmSlot) (hr : row.length ≤ asmSlot) :
    (asmProg hst hm hpre hfac extra gen row agg).HasAt asmAggBase agg := by
  intro j hj
  have hc : (asmPad asmSlot asmCore).length = asmSlot :=
    length_asmPad (by rw [length_asmCore]; decide)
  have hg' : (asmPad asmSlot gen).length = asmSlot := length_asmPad hg
  have hr' : (asmPad asmSlot row).length = asmSlot := length_asmPad hr
  simp only [asmProg, List.append_assoc]
  rw [List.getElem?_append_right (by rw [hc]; unfold asmAggBase asmSlot; omega), hc,
    List.getElem?_append_right (by rw [hg']; unfold asmAggBase asmSlot; omega), hg',
    List.getElem?_append_right (by rw [hr']; unfold asmAggBase asmSlot; omega), hr',
    show asmAggBase + j - asmSlot - asmSlot - asmSlot = j by unfold asmAggBase asmSlot; omega,
    List.getElem?_eq_getElem hj]

/-- The extra primitives sit at `asmPrimBase = 4`. -/
theorem asmProg_prim_extra (j : ℕ) :
    (asmProg hst hm hpre hfac extra gen row agg).prims[asmPrimBase + j]? = extra[j]? := by
  rw [asmPrimBase, Nat.add_comm]
  simp [asmProg]

theorem asmProg_prim_pst :
    (asmProg hst hm hpre hfac extra gen row agg).prims[0]? = some (pointwiseStabPrim hst) := rfl
theorem asmProg_prim_mem :
    (asmProg hst hm hpre hfac extra gen row agg).prims[1]? = some (membershipPrim hm) := rfl
theorem asmProg_prim_pre :
    (asmProg hst hm hpre hfac extra gen row agg).prims[2]? = some (preimagePrim hpre) := rfl
theorem asmProg_prim_fac :
    (asmProg hst hm hpre hfac extra gen row agg).prims[3]? = some (normalizedFactorPrim hfac) :=
  rfl

/-- A block of the core. -/
theorem asm_block {gs : List Expr} (i : ℕ) (hg : (asmCore.drop i).take gs.length = gs) :
    (asmProg hst hm hpre hfac extra gen row agg).HasAt i gs := by
  simpa using asmProg_hasAt_core.block i hg

/-- A single function of the core. -/
theorem asm_one {e : Expr} (i : ℕ) (hg : (asmCore.drop i).take 1 = [e]) :
    (asmProg hst hm hpre hfac extra gen row agg).funs[i]? = some e :=
  (asm_block (gs := [e]) i hg).single

theorem asm_prepAt : PrepAt (asmProg hst hm hpre hfac extra gen row agg)
    9 104 112 10 11 137 140 143 205 210 0 where
  entry := asm_one 9 rfl
  redAt := asm_block 104 rfl
  domAt := domAt_of_hasAt (asm_block 112 rfl)
  colAt := asm_one 10 rfl
  apAt := asm_block 137 rfl
  hierAt := asm_one 11 rfl
  repAt := asm_block 140 rfl
  loAt := asm_block 143 rfl
  cntAt := asm_block 205 rfl
  obAt := asm_block 210 rfl

theorem asm_liftAt : LiftAt (asmProg hst hm hpre hfac extra gen row agg) 289 112 2 3 :=
  liftAt_of_hasAt (asm_block 289 rfl)

theorem asm_directAt : DirectAt (asmProg hst hm hpre hfac extra gen row agg)
    7 99 9 104 112 10 11 137 140 143 205 210 0 12 242 270 13 273 277 280 137 286 1 289 2 3 where
  entry := asm_one 7 rfl
  sizeAt := asm_block 99 rfl
  prepAt := asm_prepAt
  cfAt := {
    entry := asm_one 12 rfl
    enAt := asm_block 242 rfl
    flAt := asm_block 270 rfl
    tfAt := asm_one 13 rfl
    cpAt := asm_block 273 rfl
    eqAt := asm_block 277 rfl
    nfAt := asm_block 280 rfl
    apAt := asm_block 137 rfl
    rgAt := asm_block 286 rfl }
  liftAt := asm_liftAt

theorem asm_freshAt : FreshAt (asmProg hst hm hpre hfac extra gen row agg) asmF
    8 9 104 112 10 11 137 140 143 205 210 0 289 2 3 where
  entry := asm_one 8 rfl
  prepAt := asm_prepAt
  liftAt := asm_liftAt

end Prog

/-! ### The concrete interface -/

/-- **The concrete `Rest`.** The constants of `Solve` come from the direct and fresh steps, the
selector bounds from `RestSel` and `GiantSel`; the works of the three missing steps are the
parameters `Wg` (general dispatcher), `Wr` (row step) and `Wa` (aggregation round). -/
noncomputable def asmRest (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (Wg Wr Wa : Node P₀ → ℝ) : Rest where
  solveK := Rest.solveKOf (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) hm
  solveD := Rest.solveDOf (pointwiseStabPrim hst) (preimagePrim hpre) (normalizedFactorPrim hfac) hm
  restSelB := fun S => restSelB S
  giantSelW := fun S => giantSelWStd hpre S
  Wgeneral := Wg
  Wrow := Wr
  Wagg := Wa

/-- **`Layout.OK` for the concrete program**, given the step specifications of the three missing
steps. Every other field is proved here. -/
theorem asm_layoutOK (hst : PointwiseStab) (hm : Membership) (hpre : Preimage)
    (hfac : NormalizedFactor) (Wg Wr Wa : Node P₀ → ℝ) (extra : List Prim)
    (gen row agg : List Expr)
    (hgen : (asmRest hst hm hpre hfac Wg Wr Wa).iface.GeneralSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmGenBase)
    (hrow : (asmRest hst hm hpre hfac Wg Wr Wa).iface.RowSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmRowBase)
    (hagg : (asmRest hst hm hpre hfac Wg Wr Wa).iface.AggSpec
      (asmProg hst hm hpre hfac extra gen row agg) asmF asmAggBase) :
    Iface.Layout.OK (asmRest hst hm hpre hfac Wg Wr Wa).iface
      (asmProg hst hm hpre hfac extra gen row agg) asmLayout := by
  set R := asmRest hst hm hpre hfac Wg Wr Wa
  set Pg := asmProg hst hm hpre hfac extra gen row agg
  have hK := R.solve_consts (pst := pointwiseStabPrim hst) (pp := preimagePrim hpre)
    (pf := normalizedFactorPrim hfac) (hm := hm) rfl rfl
  exact {
    solve_body := asm_one 0 rfl
    cont_body := asm_one 1 rfl
    giant_body := asm_one 2 rfl
    solveSel := R.solveSel (asm_block 14 rfl)
    contSel := R.contSel_built (fun _ => rfl) (asm_block 20 rfl) (asm_one 6 rfl)
      (asm_block 143 rfl) (asm_block 342 rfl) (asm_block 320 rfl)
    giantSel := R.giantSel hpre (asm_block 26 rfl) asmProg_prim_pre (fun _ => le_rfl)
    direct := Iface.directSpec R.iface Pg asmF hst hpre hfac hm asm_directAt asmProg_prim_pst
      asmProg_prim_mem asmProg_prim_pre asmProg_prim_fac hK.2
    fresh := Iface.freshSpec R.iface Pg asmF hst hpre hfac asm_freshAt asmProg_prim_pst
      asmProg_prim_pre asmProg_prim_fac hK.1
    threshold := Iface.thresholdSpec R.iface Pg asmF (asm_one 3 rfl) R.thresholdW
    orbit := Iface.orbitSpec R.iface Pg asmF (asm_one 5 rfl) (asm_block 143 rfl)
      (asm_block 320 rfl) (asm_block 338 rfl) (asm_block 273 rfl) R.orbitW
    floor := Iface.floorSpec R.iface Pg asmF (asm_one 4 rfl) R.floorW
    general := hgen
    row := hrow
    agg := hagg }

end GI.Impl
