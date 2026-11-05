module

public import Workspace.Impl.Dispatch

@[expose] public section

/-!
# The cases of the three procedures

Algorithms 4 and 5 split each procedure into guarded cases. The constructors of
`GI.Algorithm.Run` follow them. Here each case gets a guard (`CasePred`), the constructors that
its step may produce, and a named step specification (`Iface.StepSpec`).

`Solve`:
* `direct`: `|dom| ≤ N₀`; constructor `direct`; spec `DirectSpec`;
* `fresh`: `N₀ < |dom|`; constructor `fresh`; spec `FreshSpec`.

`Continue`:
* `threshold`: `|dom| ≤ N^γ`; constructor `threshold`; spec `ThresholdSpec`;
* `orbit`: above the threshold, intransitive; constructors `orbitStop`, `orbitChain`;
  spec `OrbitSpec`;
* `floor`: above the threshold, transitive, the column floor entered; constructor
  `floorReset`; spec `FloorSpec`;
* `general`: above the threshold, transitive, off the floor; constructors `dispatch` and
  `normalize` (the dispatcher computes the primitive quotient first, and then knows which of
  the two applies); spec `GeneralSpec`.

`GiantStep` (with supplied labels `L` read from the input):
* `row`: the row case `RowCase α S L`; constructors `rowTerminal`, `rowColumns`; spec `RowSpec`;
* `agg`: not the row case; constructor `aggregate`; spec `AggSpec`.

A program that places the three dispatchers, three selectors and eight step functions in its
function table and meets these specifications (`Layout.OK`) satisfies obligation (a)
(`Layout.implements`), and with (b) and (c) the trusted statement (`Layout.final`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

namespace Cases

/-- `Solve`, direct enumeration: `|dom| ≤ N₀`. -/
def direct : CasePred := ⟨fun _ S _ => S.size ≤ P₀.N₀⟩

/-- `Solve`, a fresh phase: `N₀ < |dom|`. -/
def fresh : CasePred := ⟨fun _ S _ => P₀.N₀ < S.size⟩

/-- `Continue`, at or below the phase threshold: `|dom| ≤ N^γ`. -/
def threshold : CasePred := ⟨fun _ S _ => (S.size : ℝ) ≤ (S.N : ℝ) ^ P₀.γ⟩

/-- `Continue`, intransitive above the threshold. -/
def orbit : CasePred := ⟨fun _ S _ => (S.N : ℝ) ^ P₀.γ < S.size ∧ ¬ S.Transitive⟩

/-- `Continue`, transitive above the threshold, at the column floor. -/
def floor : CasePred :=
  ⟨fun _ S _ => (S.N : ℝ) ^ P₀.γ < S.size ∧ S.Transitive ∧ S.FloorEntered⟩

/-- `Continue`, transitive above the threshold, off the column floor. -/
def general : CasePred :=
  ⟨fun _ S _ => (S.N : ℝ) ^ P₀.γ < S.size ∧ S.Transitive ∧ ¬ S.FloorEntered⟩

/-- `GiantStep`, the row case for the supplied labels. -/
def row (I : Iface) : CasePred :=
  ⟨fun e S v => ∃ (sv lv : Val) (L : SuppliedLabels S), v = .list [sv, lv] ∧ I.LabVal e S lv L ∧
    RowCase P₀.α S L⟩

/-- `GiantStep`, the aggregation case for the supplied labels. -/
def agg (I : Iface) : CasePred :=
  ⟨fun e S v => ∃ (sv lv : Val) (L : SuppliedLabels S), v = .list [sv, lv] ∧ I.LabVal e S lv L ∧
    ¬ RowCase P₀.α S L⟩

end Cases

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- The cases of `Solve`, in the order of the selector's answers. -/
def solveCases : List CasePred := [Cases.direct, Cases.fresh]

/-- The cases of `Continue`. -/
def contCases : List CasePred := [Cases.threshold, Cases.orbit, Cases.floor, Cases.general]

/-- The cases of `GiantStep`. -/
def giantCases : List CasePred := [Cases.row I, Cases.agg I]

/-- Step specification of `direct` (`Run.direct`). -/
def DirectSpec (f : ℕ) : Prop := I.StepSpec Pg F .solve Cases.direct [.direct] f
/-- Step specification of a fresh phase (`Run.fresh`). -/
def FreshSpec (f : ℕ) : Prop := I.StepSpec Pg F .solve Cases.fresh [.fresh] f
/-- Step specification of the threshold (`Run.threshold`). -/
def ThresholdSpec (f : ℕ) : Prop := I.StepSpec Pg F .cont Cases.threshold [.threshold] f
/-- Step specification of the orbit chain (`Run.orbitStop`, `Run.orbitChain`). -/
def OrbitSpec (f : ℕ) : Prop :=
  I.StepSpec Pg F .cont Cases.orbit [.orbitStop, .orbitChain] f
/-- Step specification of the floor reset (`Run.floorReset`). -/
def FloorSpec (f : ℕ) : Prop := I.StepSpec Pg F .cont Cases.floor [.floorReset] f
/-- Step specification of the general dispatcher (`Run.dispatch`, `Run.normalize`). -/
def GeneralSpec (f : ℕ) : Prop :=
  I.StepSpec Pg F .cont Cases.general [.dispatch, .normalize] f
/-- Step specification of the row step (`Run.rowTerminal`, `Run.rowColumns`). -/
def RowSpec (f : ℕ) : Prop :=
  I.StepSpec Pg F .giant (Cases.row I) [.rowTerminal, .rowColumns] f
/-- Step specification of the aggregation round (`Run.aggregate`). -/
def AggSpec (f : ℕ) : Prop := I.StepSpec Pg F .giant (Cases.agg I) [.aggregate] f

/-- The indices of the functions of an implementation of the recursion: the three dispatchers
(`F`), the three selectors and the eight step functions. -/
structure Layout where
  F : Funs
  solveSel : ℕ
  direct : ℕ
  fresh : ℕ
  contSel : ℕ
  threshold : ℕ
  orbit : ℕ
  floor : ℕ
  general : ℕ
  giantSel : ℕ
  row : ℕ
  agg : ℕ

/-- **Everything obligation (a) needs**: the dispatchers sit in the function table, and the
selectors and step functions meet their specifications. -/
structure Layout.OK (L : Layout) : Prop where
  solve_body : Pg.funs[L.F.solve]? = some (modeBody L.solveSel [L.direct, L.fresh])
  cont_body : Pg.funs[L.F.cont]? =
    some (modeBody L.contSel [L.threshold, L.orbit, L.floor, L.general])
  giant_body : Pg.funs[L.F.giant]? = some (modeBody L.giantSel [L.row, L.agg])
  solveSel : I.SelSpec Pg .solve solveCases L.solveSel
  contSel : I.SelSpec Pg .cont contCases L.contSel
  giantSel : I.SelSpec Pg .giant I.giantCases L.giantSel
  direct : I.DirectSpec Pg L.F L.direct
  fresh : I.FreshSpec Pg L.F L.fresh
  threshold : I.ThresholdSpec Pg L.F L.threshold
  orbit : I.OrbitSpec Pg L.F L.orbit
  floor : I.FloorSpec Pg L.F L.floor
  general : I.GeneralSpec Pg L.F L.general
  row : I.RowSpec Pg L.F L.row
  agg : I.AggSpec Pg L.F L.agg

/-- The three procedures meet `ModeOK`. -/
theorem Layout.modeOK {L : Layout} (h : Layout.OK I Pg L) : ∀ m, I.ModeOK Pg L.F m
  | .solve => I.modeOK_of_dispatch Pg L.F (m := .solve) h.solve_body rfl (by simp only [List.length_cons, List.length_nil]; omega) h.solveSel
      fun j hj => match j, hj with
        | 0, _ => ⟨_, h.direct⟩
        | 1, _ => ⟨_, h.fresh⟩
  | .cont => I.modeOK_of_dispatch Pg L.F (m := .cont) h.cont_body rfl (by simp only [List.length_cons, List.length_nil]; omega) h.contSel
      fun j hj => match j, hj with
        | 0, _ => ⟨_, h.threshold⟩
        | 1, _ => ⟨_, h.orbit⟩
        | 2, _ => ⟨_, h.floor⟩
        | 3, _ => ⟨_, h.general⟩
  | .giant => I.modeOK_of_dispatch Pg L.F (m := .giant) h.giant_body rfl (by simp only [List.length_cons, List.length_nil]; omega) h.giantSel
      fun j hj => match j, hj with
        | 0, _ => ⟨_, h.row⟩
        | 1, _ => ⟨_, h.agg⟩

/-- **Obligation (a) from the step specifications.** -/
theorem Layout.implements {L : Layout} (h : Layout.OK I Pg L) :
    Implements .solve Pg L.F.solve I.work :=
  I.implements Pg L.F (Layout.modeOK I Pg h)

/-- **The trusted statement from the step specifications**, the graph wrapper (b) and the work
requirement (c). -/
theorem Layout.final {L : Layout} (h : Layout.OK I Pg L) {fm : ℕ}
    (hb : GraphWrapper Pg fm L.F.solve) (hc : I.WorkReq) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  GI.Assembly.final (Layout.implements I Pg h) hb (I.workBound hc)

end Iface

end GI.Impl
