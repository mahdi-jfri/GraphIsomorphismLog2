module

public import Workspace.Impl.AggItemCiSojRectGlobal
public import Workspace.Impl.AggItemCiSojRawBranches

@[expose] public section

/-! # Installed programs for the full first-rectangle source dispatch -/

namespace GI.Impl

open GI.Lang

/-- Indices of the complete source dispatch and both finished branches. -/
structure itcsSourceIdx where
  rect : itcsRectIdx
  comp : itcsCompIdx
  f : ℕ
  front : ℕ
  fiber : ℕ
  find : ℕ
  test : ℕ
  pc : ℕ
  size : ℕ
  baltest : ℕ
  baltestB : ℕ
  imp : ℕ
  min : ℕ
  minB : ℕ
  part : ℕ
  cert : ℕ

/-- Every source-dispatch callee is the actual front/component/partition
program. The rectangle and canonical-answer pipelines are recorded separately. -/
structure itcsSourceOk (Pg : Program) (A : itcsSourceIdx) : Prop where
  rect : itcsRectOk Pg A.rect
  comp : itcsCompOk Pg A.comp
  body : Pg.funs[A.f]?=some (itcsStartF A.front A.pc A.rect.query.rng A.rect.bal A.baltest A.imp A.part A.cert A.rect.f)
  front : Pg.funs[A.front]?=some (itcsFrontF A.rect.query.rng A.fiber A.find)
  fiber : Pg.HasAt A.fiber (filterFuns A.fiber A.rect.fiberB)
  find : Pg.HasAt A.find (findFuns A.find A.test)
  test : Pg.funs[A.test]?=some (itcsTestF A.pc A.size)
  pc : Pg.funs[A.pc]?=some itcqPcF
  size : Pg.funs[A.size]?=some (itcsSizeF A.comp.f A.comp.c1.sz)
  baltest : Pg.HasAt A.baltest (allFuns A.baltest A.baltestB)
  baltestB : Pg.funs[A.baltestB]?=some (itcsBalTestF A.comp.c1.sz)
  imp : Pg.funs[A.imp]?=some (itcsImpPartF A.comp.c1.rng A.comp.f A.min A.comp.c1.f)
  min : Pg.HasAt A.min (allFuns A.min A.minB)
  minB : Pg.funs[A.minB]?=some (itcsMinF A.rect.fiberB A.comp.c1.sz)
  part : Pg.funs[A.part]?=some (itcsBalPartF A.rect.query.rng A.rect.bal A.rect.part.f)

end GI.Impl
