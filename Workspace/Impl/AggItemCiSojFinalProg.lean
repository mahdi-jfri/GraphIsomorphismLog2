import Workspace.Impl.AggItemCiSojFinalSpec

/-! # Installed program bodies discharge the complete answer-finalizer contract -/

namespace GI.Impl

open GI.Lang
open GI.Cited (NormalizedFactor)

/-- Indices of all actual saved-answer processing programs. -/
structure itcsFinalIdx where
  f : ℕ
  rows : ℕ
  rng : ℕ
  rowMap : ℕ
  rowB : ℕ
  project : ℕ
  lift : ℕ
  groupMap : ℕ
  generatorMap : ℕ
  compose : ℕ
  shift : ℕ
  split : ℕ
  factor : ℕ
  filter : ℕ
  nonempty : ℕ
  firstMap : ℕ
  firstB : ℕ
  groupBuild : ℕ
  inverse : ℕ
  buildMap : ℕ
  append : ℕ
  overMap : ℕ
  overB : ℕ

/-- All finalizer calls are the actual normalized-factor, generator projection,
filter, group-construction and overcoset programs. -/
structure itcsFinalOk (Pg : Program) (A : itcsFinalIdx) (hfac : NormalizedFactor) : Prop where
  body : Pg.funs[A.f]?=some (itcsFinishF A.rows A.filter A.firstMap A.groupBuild A.overMap)
  rows : Pg.funs[A.rows]?=some (itcsRowsF A.rng A.rowMap)
  rng : Pg.HasAt A.rng (rangeFuns A.rng)
  rowMap : Pg.HasAt A.rowMap (mapFuns A.rowMap A.rowB)
  rowB : Pg.funs[A.rowB]?=some (itcsRowF A.project)
  project : Pg.funs[A.project]?=some (itcsProjectF A.lift A.groupMap A.compose)
  lift : Pg.funs[A.lift]?=some (liftLabF A.shift A.split A.factor)
  shift : ShiftAt Pg A.shift
  split : Pg.HasAt A.split (pSplitFuns A.split)
  factor : Pg.prims[A.factor]?=some (normalizedFactorPrim hfac)
  groupMap : Pg.funs[A.groupMap]?=some (itcsGroupMapF A.generatorMap)
  generatorMap : Pg.HasAt A.generatorMap (mapFuns A.generatorMap A.lift)
  compose : Pg.HasAt A.compose (composeFuns A.compose)
  filter : Pg.HasAt A.filter (filterFuns A.filter A.nonempty)
  nonempty : Pg.funs[A.nonempty]?=some itcsRowNE
  firstMap : Pg.HasAt A.firstMap (mapFuns A.firstMap A.firstB)
  firstB : Pg.funs[A.firstB]?=some krFstF
  groupBuild : Pg.funs[A.groupBuild]?=some (itcsGroupBuildF A.inverse A.buildMap A.append)
  inverse : Pg.HasAt A.inverse (invFuns A.inverse)
  buildMap : Pg.HasAt A.buildMap (mapFuns A.buildMap A.compose)
  append : Pg.HasAt A.append (appendFuns A.append)
  overMap : Pg.HasAt A.overMap (mapFuns A.overMap A.overB)
  overB : Pg.funs[A.overB]?=some (itcsOverF A.compose)

/-- The complete finalizer contract follows from these actual installations.
All normalized-factor membership and input-size premises are discharged by the
proved row-builder contract, rather than assumed here. -/
theorem itcs_final_ok_spec {Pg : Program} {A : itcsFinalIdx} {hfac : NormalizedFactor}
    (h : itcsFinalOk Pg A hfac) : itcsFinalSpec Pg A.f (normalizedFactorPrim hfac) := by
  have rows : itcsRowsSpec Pg A.rows (normalizedFactorPrim hfac) := by
    intro Ω C k
    exact itcs_rows_spec hfac h.rows h.rng h.rowMap h.rowB h.project h.lift h.shift h.split
      h.factor h.groupMap h.generatorMap h.compose
  intro Ω C k
  exact itcs_final_spec (normalizedFactorPrim hfac) rows h.body h.filter h.nonempty h.firstMap h.firstB
    h.groupBuild h.inverse h.buildMap h.compose h.append h.overMap h.overB

end GI.Impl
