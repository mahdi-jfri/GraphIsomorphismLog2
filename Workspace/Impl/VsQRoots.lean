import Workspace.Impl.VsQPoly
import Workspace.Impl.VsBFld
import Workspace.Impl.VsBOrb
import Workspace.Impl.VsQApp
import Workspace.Impl.VsQPaste
import Workspace.Impl.VsQPhi
import Workspace.Impl.VsQLink

/-!
# The layout of the whole program

The index records and layout facts of the parts that the specs take as explicit arguments: the
entry, the driver with its apply and paste programs, the analysis with its branches, the A-loop,
and the evaluation `φ`. The layouts of the inner parts are the records of the specs themselves.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The indices of the evaluation `φ`. -/
structure VsQPhiX where
  (phi j gl : ℕ)

structure VsQPhiLay (P : Program) (x : VsQPhiX) (hcm : ConstructiveMembership) : Prop where
  hphi : P.HasAt x.phi (vsQPhiFuns x.phi x.j x.gl (x.gl + 2))
  hj : P.prims[x.j]? = some (linMembershipPrim hcm)
  hgl : P.HasAt x.gl (vsQGLFuns x.gl)

/-- The indices of the entry. -/
structure VsQTopX where
  (top rng fold st idp rep tbm it tr red jm tl drv : ℕ)

structure VsQTopLay (P : Program) (x : VsQTopX) (hm : Membership) : Prop where
  hf : P.funs[x.top]? = some (vsQTopE x.rng x.fold x.idp x.rep x.tbm x.red x.drv x.tl)
  hrng : P.HasAt x.rng (rangeFuns x.rng)
  hfold : P.HasAt x.fold (foldlFuns x.fold x.st)
  hst : P.funs[x.st]? = some vsQFactStepE
  hidp : P.HasAt x.idp (vsWIdFuns x.idp)
  hrep : P.HasAt x.rep (replicateFuns x.rep)
  htbm : P.HasAt x.tbm (mapFuns x.tbm x.it)
  hit : P.funs[x.it]? = some (vsQTblItE x.tr)
  htr : P.HasAt x.tr (vsQTrFuns x.tr)
  hred : P.HasAt x.red (reduceFuns x.red x.jm)
  hjm : P.prims[x.jm]? = some (membershipPrim hm)
  htl : P.HasAt x.tl (linTailFuns x.tl)

/-- The indices of the driver, with its apply and paste programs. -/
structure VsQDrvX where
  (drv ana ai cmp paste inv mm phi fd pinv pmp app mkg red jm pcmp : ℕ)

structure VsQDrvLay (P : Program) (x : VsQDrvX) (hm : Membership) : Prop where
  hdrv : P.HasAt x.drv (vsQDrvFuns x.drv x.ana x.ai x.cmp x.paste)
  hcmp : P.HasAt x.cmp (composeFuns x.cmp)
  hai : P.funs[x.ai]? = some (vsQAppE x.inv x.phi (x.mm + 3))
  hinv : P.HasAt x.inv (invFuns x.inv)
  hmm : P.HasAt x.mm (vsFMatMulFuns x.mm)
  hp : P.funs[x.paste]? = some (vsQPasteE x.fd x.pinv x.pmp x.app x.mkg x.red)
  hfd : P.HasAt x.fd (findFuns x.fd (x.fd + 3))
  ht : P.funs[x.fd + 3]? = some vsQPTestE
  hpinv : P.HasAt x.pinv (invFuns x.pinv)
  hmp : P.HasAt x.pmp (mapFuns x.pmp (x.pmp + 3))
  hmpE : P.funs[x.pmp + 3]? = some (vsQPMapE x.pcmp)
  hpc : P.HasAt x.pcmp (composeFuns x.pcmp)
  happ : P.HasAt x.app (appendFuns x.app)
  hmkg : P.HasAt x.mkg (mkGroupFuns x.mkg)
  hred : P.HasAt x.red (reduceFuns x.red x.jm)
  hjm : P.prims[x.jm]? = some (membershipPrim hm)

/-- The indices of the field-line base. -/
structure VsBFldX where
  (f prep c0 cM unit appd rng chA chB co lin sotA sotB bA bB phi jp jm fd tst c0b m eqN tau dA red sc sv mI fI
    mF fF sv2 rp mm fl ch cmp dB mc cr : ℕ)

/-- The indices of the analysis. -/
structure VsQAnaX where
  (ana lcp orb ojp ojm abb al ctx flm it fl rws rep abt fo no fi nc comp loc eq phi : ℕ) (fld : VsBFldX)

structure VsQAnaLay (P : Program) (x : VsQAnaX) (hps : PointwiseStab) (hm : Membership) : Prop where
  hf : P.funs[x.ana]? = some (vsQAnaE x.lcp x.orb x.ctx x.abt x.abb x.al)
  hctx : P.funs[x.ctx]? = some (vsPCtxE x.flm x.rws x.rep)
  hflm : P.HasAt x.flm (mapFuns x.flm x.it)
  hit : P.funs[x.it]? = some (vsPFlItemE x.fl)
  hfl : P.HasAt x.fl (vsWFlatFuns x.fl)
  hrws : P.HasAt x.rws (vsWRowsFuns x.rws)
  hrep : P.HasAt x.rep (replicateFuns x.rep)
  habt : P.funs[x.abt]? = some (vsPAbE x.fo)
  hfo : P.HasAt x.fo (findFuns x.fo x.no)
  hno : P.funs[x.no]? = some (vsPNoE x.fi)
  hfi : P.HasAt x.fi (findFuns x.fi x.nc)
  hnc : P.funs[x.nc]? = some (vsPNcE x.comp x.loc x.eq)
  hcomp : P.HasAt x.comp (composeFuns x.comp)
  hloc : P.funs[x.loc]? = some (vsPLocE x.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  heq : P.HasAt x.eq (vsPEqFuns x.eq)
  hlcp : P.HasAt x.lcp (vsQLCFuns x.lcp x.phi)
  horb : P.HasAt x.orb (vsBOrbFuns x.orb x.phi x.ojp x.ojm)
  hojp : P.prims[x.ojp]? = some (pointwiseStabPrim hps)
  hojm : P.prims[x.ojm]? = some (membershipPrim hm)
  habb : P.HasAt x.abb (vsQAbFuns x.abb x.fld.f)
  hfld : VsBFldAt P hps hm x.fld.f x.fld.prep x.fld.c0 x.fld.cM x.fld.unit x.fld.appd x.fld.rng x.fld.chA
    x.fld.chB x.fld.co x.fld.lin x.fld.sotA x.fld.sotB x.fld.bA x.fld.bB x.fld.phi x.fld.jp x.fld.jm x.fld.fd
    x.fld.tst x.fld.c0b x.fld.m x.fld.eqN x.fld.tau x.fld.dA x.fld.red x.fld.sc x.fld.sv x.fld.mI x.fld.fI
    x.fld.mF x.fld.fF x.fld.sv2 x.fld.rp x.fld.mm x.fld.fl x.fld.ch x.fld.cmp x.fld.dB x.fld.mc x.fld.cr

/-- The indices of the A-loop (without the hard case and the `Q₈` continuation). -/
structure VsQALX where
  (al s4 st4 hard q8c : ℕ) (x2 : VsQA2AX) (x3 : VsQA3X) (x4 : VsPStep4X)

structure VsQALLay (P : Program) (x : VsQALX) (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) : Prop where
  hf : P.funs[x.al]? = some (vsQALE x.x2.f x.x3.f x.s4 x.al)
  L2 : VsQA2AAt P x.x2 hps hm hmb
  L3 : VsQA3At P x.x3 hps hm
  h4 : P.funs[x.s4]? = some (vsQA4E x.st4 x.hard x.q8c)
  hst4 : P.funs[x.st4]? = some (vsPStep4E x.x4.ctxP x.x4.der x.x4.x2.x3.x4.ab x.x4.x2.x3.x4.grow
    x.x4.x2.x3.tl x.x4.s2)
  L4 : VsPStep4Lay P hn hd x.x4

end GI.Impl
