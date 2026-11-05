module

public import Workspace.Impl.AggItemCiSojQueryGlobal
public import Workspace.Impl.AggItemCiSojCertTables
public import Workspace.Impl.AggItemCiSojRectProg

@[expose] public section

/-! # Installed bodies for the certified rectangle controller -/

namespace GI.Impl

open GI.Lang

/-- Indices of the rectangle controller and its side-table programs. -/
structure itcsRectIdx where
  query : itcsQueryIdx
  part : ItciIdx
  f : ℕ
  bal : ℕ
  balB : ℕ
  fiberB : ℕ
  sides : ℕ
  sideB : ℕ
  guard : ℕ
  count : ℕ
  align : ℕ
  fix : ℕ
  fixMap : ℕ
  fixB : ℕ
  fixGen : ℕ
  markW : ℕ
  markR : ℕ
  markWB : ℕ
  markRB : ℕ
  rep : ℕ

/-- The rectangle controller uses the actual partition, marker, fixing-group,
and physical-query programs already proved above. -/
structure itcsRectOk (Pg : Program) (A : itcsRectIdx) : Prop where
  query : itcsQueryOk Pg A.query
  part : ItciOk Pg A.part
  body : Pg.funs[A.f]?=some (itcsRectPrepF A.query.rng A.bal A.sides A.guard A.align A.fix
    A.markW A.markR A.rep A.query.ask)
  bal : Pg.HasAt A.bal (mapFuns A.bal A.balB)
  balB : Pg.funs[A.balB]?=some (itcsBalB A.fiberB)
  fiberB : Pg.funs[A.fiberB]?=some itcqFbT
  sides : Pg.HasAt A.sides (mapFuns A.sides A.sideB)
  sideB : Pg.funs[A.sideB]?=some itcsSideF
  guard : Pg.funs[A.guard]?=some (itcsGuardF A.count)
  count : Pg.HasAt A.count (countFuns A.count)
  align : Pg.funs[A.align]?=some (itcsAlignF A.part.f)
  fix : Pg.funs[A.fix]?=some (itcsFixProgF A.query.rng A.fixMap A.fixGen)
  fixMap : Pg.HasAt A.fixMap (mapFuns A.fixMap A.fixB)
  fixB : Pg.funs[A.fixB]?=some itcsFixMarkF
  fixGen : Pg.funs[A.fixGen]?=some (itcsFixGenF A.part.f)
  markW : Pg.HasAt A.markW (mapFuns A.markW A.markWB)
  markR : Pg.HasAt A.markR (mapFuns A.markR A.markRB)
  markWB : Pg.funs[A.markWB]?=some (itcsMarkF 2)
  markRB : Pg.funs[A.markRB]?=some (itcsMarkF 1)

end GI.Impl
