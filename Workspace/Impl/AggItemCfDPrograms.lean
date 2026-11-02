import Workspace.Impl.AggItemCfDAt
import Workspace.Impl.AggItemCfDCost

namespace GI.Impl

open GI.Lang GI.Cited

/-- Scan the prefixes in increasing order, then read the object at the first hit. -/
def itCfDCoreF (fh rb atf : ℕ) : Expr :=
  .letE (.call fh (mk2 (.var 0) (.call rb (.get (.var 0) (.nat 3)))))
    (.ite (.arith .lt (.var 1) (.get (.var 0) (.nat 3)))
      (.call atf (mk2 (.var 0) (.var 1))) (.snoc .nil (.nat 0)))

/-- The design object program on `[q,κ,col,t]`. -/
def itCfDesF (core : ℕ) : Expr :=
  .ite (arg 1)
    (.ite (.arith .lt (arg 1) (.length (arg 3)))
      (.call core (mk4 (arg 2) (arg 3) (arg 0) (arg 1)))
      (.snoc .nil (.nat 0)))
    (.snoc .nil (.nat 0))

/-- Function indices used by the design program. -/
structure ItCfDIdx where
  rb : ℕ
  cf : ℕ
  hor : ℕ
  vm : ℕ
  vmap : ℕ
  vf : ℕ
  dv : ℕ
  dvv : ℕ
  cb : ℕ
  ad : ℕ
  fd : ℕ
  rf : ℕ
  df : ℕ
  fr : ℕ
  adr : ℕ
  sp : ℕ
  hit2 : ℕ
  hit : ℕ
  fh : ℕ
  bl : ℕ
  bm : ℕ
  br : ℕ
  brm : ℕ
  bce : ℕ
  tb : ℕ
  tm : ℕ
  tr : ℕ
  trm : ℕ
  tce : ℕ
  atf : ℕ
  core : ℕ

/-- Only function-table and module-placement facts. No semantic program
specifications are assumed in this interface. -/
structure ItCfDOk (P : Program) (I : ItCfDIdx) : Prop where
  rb : P.HasAt I.rb (rangeFuns I.rb)
  cf : P.funs[I.cf]? = some (GI.Impl.stDColF I.hor)
  hor : P.HasAt I.hor (GI.Impl.stDHorFuns I.hor)
  vm : P.funs[I.vm]? = some (GI.Impl.stDVMapF I.vmap I.rb)
  vmap : P.HasAt I.vmap (mapFuns I.vmap I.vf)
  vf : P.funs[I.vf]? = some (GI.Impl.stDVF I.cf)
  dv : P.funs[I.dv]? = some (GI.Impl.stDDomF I.dvv)
  dvv : P.funs[I.dvv]? = some (GI.Impl.stDDomVF I.cb)
  cb : P.HasAt I.cb (countFuns I.cb)
  ad : P.HasAt I.ad (anyFuns I.ad I.dv)
  fd : P.HasAt I.fd (findFuns I.fd I.dv)
  rf : P.funs[I.rf]? = some GI.Impl.stDRefF
  df : P.funs[I.df]? = some (GI.Impl.stDDifF I.rf I.cf)
  fr : P.HasAt I.fr (findFuns I.fr I.rf)
  adr : P.HasAt I.adr (anyFuns I.adr I.df)
  sp : P.funs[I.sp]? = some (GI.Impl.stDSplitF I.fd I.fr I.adr I.rb I.cf)
  hit2 : P.funs[I.hit2]? = some (GI.Impl.stDHit2F I.ad I.rb I.sp)
  hit : P.funs[I.hit]? = some (GI.Impl.stDHitF I.hit2 I.vm)
  fh : P.HasAt I.fh (findFuns I.fh I.hit)
  bl : P.funs[I.bl]? = some (itCfRTableF I.bm I.rb)
  bm : P.HasAt I.bm (mapFuns I.bm I.br)
  br : P.funs[I.br]? = some (itCfRRowF I.brm I.rb)
  brm : P.HasAt I.brm (mapFuns I.brm I.bce)
  bce : P.funs[I.bce]? = some itCfDBlockCellF
  tb : P.funs[I.tb]? = some (itCfRTableF I.tm I.rb)
  tm : P.HasAt I.tm (mapFuns I.tm I.tr)
  tr : P.funs[I.tr]? = some (itCfRRowF I.trm I.rb)
  trm : P.HasAt I.trm (mapFuns I.trm I.tce)
  tce : P.funs[I.tce]? = some (itCfDPairCellF I.cf)
  atf : P.funs[I.atf]? = some (itCfDAtF I.vm I.ad I.fd I.rb I.bl I.tb)
  core : P.funs[I.core]? = some (itCfDCoreF I.fh I.rb I.atf)

end GI.Impl
