module

public import Workspace.Impl.AggItemCiSojPhysicalData

@[expose] public section

/-! # Exact physical data of the model's inherited rectangle query -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encGroup)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

open Classical in
/-- The complete physical-data program computes the physical group, inherited
domain, and stored graph homomorphism context in their original positions. -/
theorem itcs_physical_data_exact {Pg : Program}
    {f gp fm fst mk lc sw hv gr en fsm rng dom db : ℕ}
    (hf : Pg.funs[f]? = some (itcsPhysicalDataF gp lc rng dom))
    (hgp : Pg.funs[gp]? = some (itcsPhysF fm mk))
    (hfm : Pg.HasAt fm (mapFuns fm fst)) (hfst : Pg.funs[fst]? = some krFstF)
    (hmk : Pg.HasAt mk (mkGroupFuns mk))
    (hlc : Pg.funs[lc]? = some (itcsSwapLcF sw hv)) (hsw : Pg.HasAt sw (swapMapFuns sw))
    (hhv : Pg.funs[hv]? = some (itHvLcF rng gr fsm))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hgr : Pg.funs[gr]? = some (grpF en mk))
    (hen : Pg.HasAt en (pEncMapFuns en)) (hhfm : Pg.HasAt fsm (fstMapFuns fsm))
    (hd : Pg.HasAt dom (mapFuns dom db)) (hdb : Pg.funs[db]? = some itcsDomB)
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (hk : 1 ≤ k)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (sv : List Val)
    (hsvk : sv[0]? = some (.nat k))
    (hsvd : sv[2]? = some (encFun fun i => if e.symm i ∈ S.dom then 1 else 0)) :
    let cells := encFun fun i => rcCellCode (rep.cell (e.symm i))
    let inp := Val.list [.list sv,.nat L.q,.list (hs.map pairV),cells]
    FunDet Pg f inp (.list [encGroup (hs.map Prod.fst),
      encFun (fun i => if e.symm i ∈ rep.Δ then 1 else 0),liftLabCtx L.q k (hs.map Prod.swap)])
      (itcsPhysicalDataC inp.wt (itcsPhysC (pM k L.q hs)) (itcsSwapLcC (pM k L.q hs))
        (7000*(k+1)^3) (itcsDomC k L.q)) := by
  dsimp only
  exact itcs_physical_data_prog hf sv (.nat L.q) (.list (hs.map pairV))
    (encFun fun i => rcCellCode (rep.cell (e.symm i))) (.nat k)
    (encFun fun i => if e.symm i ∈ S.dom then 1 else 0)
    (encGroup (hs.map Prod.fst)) (liftLabCtx L.q k (hs.map Prod.swap))
    (natList (List.range k)) (encFun fun i => if e.symm i ∈ rep.Δ then 1 else 0) hsvk hsvd
    (itcs_phys_prog hgp hfm hfst hmk hs)
    (itcs_swap_lc_spec hlc hsw hhv hr hgr hen hmk hhfm hs)
    (range_det hr k) (itcs_dom_prog hd hdb e rep hk)

end GI.Impl
