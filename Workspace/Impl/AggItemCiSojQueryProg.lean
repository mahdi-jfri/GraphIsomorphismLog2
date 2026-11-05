module

public import Workspace.Impl.AggItemCiSojDataBound
public import Workspace.Impl.AggItemCiSojColorsBound
public import Workspace.Impl.AggItemCiSojAskGlobal

@[expose] public section

/-! # Installed program bodies for the rectangle's actual physical queries -/

namespace GI.Impl

open GI.Lang

/-- Indices of the actual query constructor and its table/group libraries. -/
structure itcsQueryIdx where
  ask : ℕ
  data : ℕ
  colors : ℕ
  gp : ℕ
  fm : ℕ
  fst : ℕ
  group : ℕ
  lc : ℕ
  sw : ℕ
  hv : ℕ
  gr : ℕ
  en : ℕ
  fsm : ℕ
  rng : ℕ
  dom : ℕ
  db : ℕ
  cmp : ℕ
  pull : ℕ
  cb : ℕ
  bit : ℕ
  state : ℕ

/-- All query constructors are the displayed programs, with their actual
standard libraries installed at the specified indices. -/
structure itcsQueryOk (Pg : Program) (Q : itcsQueryIdx) : Prop where
  ask : Pg.funs[Q.ask]?=some (itcsAskF Q.data Q.colors)
  data : Pg.funs[Q.data]?=some (itcsPhysicalDataF Q.gp Q.lc Q.rng Q.dom)
  colors : Pg.funs[Q.colors]?=some (itcsColorsStateF Q.cmp Q.rng Q.pull Q.state)
  gp : Pg.funs[Q.gp]?=some (itcsPhysF Q.fm Q.group)
  fm : Pg.HasAt Q.fm (mapFuns Q.fm Q.fst)
  fst : Pg.funs[Q.fst]?=some krFstF
  group : Pg.HasAt Q.group (mkGroupFuns Q.group)
  lc : Pg.funs[Q.lc]?=some (itcsSwapLcF Q.sw Q.hv)
  sw : Pg.HasAt Q.sw (swapMapFuns Q.sw)
  hv : Pg.funs[Q.hv]?=some (itHvLcF Q.rng Q.gr Q.fsm)
  rng : Pg.HasAt Q.rng (rangeFuns Q.rng)
  gr : Pg.funs[Q.gr]?=some (grpF Q.en Q.group)
  en : Pg.HasAt Q.en (pEncMapFuns Q.en)
  fsm : Pg.HasAt Q.fsm (fstMapFuns Q.fsm)
  dom : Pg.HasAt Q.dom (mapFuns Q.dom Q.db)
  db : Pg.funs[Q.db]?=some itcsDomB
  cmp : Pg.HasAt Q.cmp (composeFuns Q.cmp)
  pull : Pg.HasAt Q.pull (mapFuns Q.pull Q.cb)
  cb : Pg.funs[Q.cb]?=some (itcsPullB Q.bit)
  bit : Pg.funs[Q.bit]?=some itcsPullF
  state : Pg.funs[Q.state]?=some itcsStateF

end GI.Impl
