module

public import Workspace.Impl.AggItemCiSojAskFrame
public import Workspace.Impl.AggItemCiSojStartScalar

@[expose] public section

/-! # The actual initial request fits the global item and frame budgets -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- Convert the actual data and query constructors to the common global bound.
The returned frame cap is precisely the one required by `itcs_rel_enter`. -/
theorem itcs_ask_global {Pg : Program} {f data colors Cd Cq : ℕ}
    (hf : Pg.funs[f]?=some (itcsAskF data colors)) (F : itcsQFrame e S L)
    (sv v side xt yt : Val) (xc yc : List Val) (hx : xc[0]?=some xt) (hy : yc[0]?=some yt)
    (hd : FunDet Pg data (.list [sv,.nat L.q,.list (F.hs.map pairV),
      encFun fun i => rcCellCode (F.rep.cell (e.symm i))])
      (.list [encGroup (F.hs.map Prod.fst),encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),
        liftLabCtx L.q k (F.hs.map Prod.swap)]) Cd)
    (hq : ∀ t : permitted F.W F.R,
      FunDet Pg colors (.list [sv,encGroup (F.hs.map Prod.fst),
        encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),xt,yt,v,.nat L.q,
        encFun (fun i => rcCellCode (F.rep.cell (e.symm i))),encPerm F.a₀.val,encPerm t.val.val]) (F.query t) Cq)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W : ℕ)
    (hCd : Cd≤(itcsGrow pf Bc Br hBc hBr)^[64] (W+100))
    (hCq : Cq≤(itcsGrow pf Bc Br hBc hBr)^[64] (W+100))
    (hans : ansW k≤(itcsGrow pf Bc Br hBc hBr)^[65] (W+100))
    (hin : (Val.list [sv,.nat L.q,.list xc,.list yc,v,encPerm F.a₀.val,
      .list ((itciMs (itcsFixColor F.W) (itciOt (itcsFixColor F.W))).map encPerm),
      rcRepVal e F.rep F.hs,encPerm (1:Perm (Fin L.q)),side]).wt≤
        (itcsGrow pf Bc Br hBc hBr)^[64] (W+100)) :
    let inp := Val.list [sv,.nat L.q,.list xc,.list yc,v,encPerm F.a₀.val,
      .list ((itciMs (itcsFixColor F.W) (itciOt (itcsFixColor F.W))).map encPerm),
      rcRepVal e F.rep F.hs,encPerm (1:Perm (Fin L.q)),side]
    FunDet Pg f inp (itcsAskV (F.query 1) F.payload (.list F.pending))
      ((itcsGrow pf Bc Br hBc hBr)^[65] (W+100)) ∧
      F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (W+100) := by
  dsimp only
  have call := itcs_ask_frame hf F sv v side xt yt xc yc hx hy hd hq
  have hc := itcs_budget_linear pf Bc Br hBc hBr W 64 (itcs_ask_cost_scalar hin hCd hCq hCq)
  have call' := call.mono hc
  exact ⟨call',itcs_budget_frame F pf Bc Br hBc hBr W (i:=65) (by decide)
    (itcs_det_weight call') hans⟩

end GI.Impl
