import Workspace.Impl.AggItemCiSojRepWt

/-! # The physical-data call is bounded by the paid representation value -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encGroup)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- Linear scalar constructor bound for four paid data fields. -/
theorem itcs_data_four (a b c d : Val) {n : ℕ}
    (ha : a.wt≤ n) (hb : b.wt≤ n) (hc : c.wt≤ n) (hd : d.wt≤ n) :
    (Val.list [a,b,c,d]).wt≤10^9*(n+100) := by
  have h := wt_list4_le a b c d
  omega

/-- Every structural input to physical-data construction comes from the parent
or the paid representation value. The original-position domain is retained. -/
theorem itcs_physical_frame_bounded {Pg : Program}
    {f gp fm fst mk lc sw hv gr en fsm rng dom db n : ℕ}
    (hf : Pg.funs[f]?=some (itcsPhysicalDataF gp lc rng dom))
    (hgp : Pg.funs[gp]?=some (itcsPhysF fm mk))
    (hfm : Pg.HasAt fm (mapFuns fm fst)) (hfst : Pg.funs[fst]?=some krFstF)
    (hmk : Pg.HasAt mk (mkGroupFuns mk))
    (hlc : Pg.funs[lc]?=some (itcsSwapLcF sw hv)) (hsw : Pg.HasAt sw (swapMapFuns sw))
    (hhv : Pg.funs[hv]?=some (itHvLcF rng gr fsm))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hgr : Pg.funs[gr]?=some (grpF en mk))
    (hen : Pg.HasAt en (pEncMapFuns en)) (hhfm : Pg.HasAt fsm (fstMapFuns fsm))
    (hd : Pg.HasAt dom (mapFuns dom db)) (hdb : Pg.funs[db]?=some itcsDomB)
    (F : itcsQFrame e S L) (sv : List Val)
    (hsvk : sv[0]?=some (.nat k))
    (hsvd : sv[2]?=some (encFun fun i => if e.symm i∈S.dom then 1 else 0))
    (wsv : (Val.list sv).wt≤ n) (wq : (Val.nat L.q).wt≤ n)
    (wrep : (rcRepVal e F.rep F.hs).wt≤ n)
    (cg : itcsPhysC (pM k L.q F.hs)≤ n) (cl : itcsSwapLcC (pM k L.q F.hs)≤ n)
    (cr : 7000*(k+1)^3≤ n) (cd : itcsDomC k L.q≤ n) :
    FunDet Pg f (.list [.list sv,.nat L.q,.list (F.hs.map pairV),
      encFun fun i => rcCellCode (F.rep.cell (e.symm i))])
      (.list [encGroup (F.hs.map Prod.fst),encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),
        liftLabCtx L.q k (F.hs.map Prod.swap)]) (10^9*(10^9*(n+100)+100)) := by
  have hn : n≤10^9*(n+100) := (Nat.le_add_right n 100).trans (Nat.le_mul_of_pos_left _ (by decide : 0<10^9))
  have whs := itcs_frame_pairs_weight F wrep
  have wc := itcs_frame_cells_weight F wrep
  have wi : (Val.list [.list sv,.nat L.q,.list (F.hs.map pairV),
      encFun fun i => rcCellCode (F.rep.cell (e.symm i))]).wt≤10^9*(n+100) := itcs_data_four _ _ _ _ wsv wq whs wc
  have hk : 1≤ k := (by decide : 1≤2).trans (itcs_query_k e F.rep F.conds.2.2.1 F.conds.2.2.2.1)
  have raw := itcs_physical_data_exact hf hgp hfm hfst hmk hlc hsw hhv hr hgr hen hhfm hd hdb
    e F.rep hk F.hs sv hsvk hsvd
  have cost := itcs_physical_cost_scalar wi (cg.trans hn) (cl.trans hn) (cr.trans hn) (cd.trans hn)
  exact raw.mono cost

end GI.Impl
