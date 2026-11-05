module

public import Workspace.Impl.VsHCProd
public import Workspace.Impl.VsHCTrans
public import Workspace.Impl.VsHCSize

@[expose] public section

namespace GI.Impl

open GI.Lang GI.Cited

/-- The nonrecursive continuation after the first `Q₈`.

The first two calls multiply the transversals and test the smaller centralizer.
The nonabelian branch runs step 4 once. A second `Q₈` goes directly to the product split. -/
def vsHCE (tr ab st4 hard prod : ℕ) : Expr :=
  .letE (.call tr (mk2 (.get (arg 1) (.nat 7)) (.get (arg 2) (.nat 1))))
  (.letE (.call ab (mk2 (arg 1) (.get (arg 2) (.nat 2))))
  (.ite (.var 2)
    (mk4 (.nat 1) (.var 1) (.get (arg 2) (.nat 2)) (mk1 (.get (arg 1) (.nat 2))))
    (.letE (.call st4 (vsPMk5 (arg 0) (.get (arg 1) (.nat 5)) (.get (arg 1) (.nat 10))
        (.get (arg 2) (.nat 2)) (.var 1)))
    (.ite (.get (.var 3) (.nat 0))
      (.letE (.call hard (mk2 (arg 0) (.get (.var 3) (.nat 1))))
        (.ite (.arith .eq (.get (.var 4) (.nat 0)) (.nat 2))
          (.call prod (mk3 (arg 0) (arg 1) (.get (.var 3) (.nat 1))))
          (.var 4)))
      (.var 3)))))

/-- The hard-case and continuation indices. -/
structure VsHContX where
  (h : VsHHX) (st : VsPStep4X) (tr : VsHCTransX)
  (q8c ab head prod st4 : ℕ)

/-- All links needed for the hard case and its nonrecursive continuation. -/
structure VsHContLay (P : Program) (x : VsHContX) (phi : ℕ)
    (hps : PointwiseStab) (hm : Membership) (hn : NormalClosure) (hd : DerivedSubgroup) : Prop where
  H : VsHHardLink P x.h phi hps hm
  S : VsPStep4Lay P hn hd x.st
  T : VsHCTransLay P x.tr
  hq : P.funs[x.q8c]? = some (vsHCE x.tr.f x.ab x.st4 x.h.hard x.prod)
  hab : P.funs[x.ab]? = some (vsHCAbE x.h.f.ctx x.st.x2.x3.x4.ab)
  hhead : P.funs[x.head]? = some (vsHCHeadE x.h.fr)
  hprod : P.funs[x.prod]? = some (vsHCProdE x.head x.tr.comp x.h.pp.ps x.h.w.f)
  hst4 : P.funs[x.st4]? = some
    (vsPStep4E x.st.ctxP x.st.der x.st.x2.x3.x4.ab x.st.x2.x3.x4.grow x.st.x2.x3.tl x.st.s2)
  pStep : x.st.x2.x3.x4.d.o.phi = phi

/-- The continuation cost is linear in the costs of its bounded number of calls. -/
noncomputable def vsHCQ (hps : PointwiseStab) (hm : Membership) (hn : NormalClosure)
    (hd : DerivedSubgroup) (Cφ : ℕ) (I : VecStabInst) (S : ℕ) : ℕ :=
  10 ^ 8 * (vsHHardCH hps hm Cφ I S + vsPStep4Cost (I := I) Cφ hn hd S +
    10 ^ 7 * (vsPN S + 1) * (10 ^ 9 * S ^ 8) + vsHCAbCost Cφ S +
    10 ^ 12 * (1000 * S ^ 2 + 1) ^ 7 + vsHCProdCost hps hm I.n Cφ S +
    10 ^ 30 * (S + 1) ^ 30)

end GI.Impl
