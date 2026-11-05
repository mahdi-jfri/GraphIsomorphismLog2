module

public import Workspace.Impl.AggItemCiSojColorsState
public import Workspace.Impl.AggItemCiSojPL
public import Workspace.Impl.AggItemCiSojQuery

@[expose] public section

/-! # The table pipeline constructs the exact inherited rectangle query -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Cost of the direct inherited-state encoder on its actual input. -/
def itcsStateC (sv gv dv xv yv : Val) : ℕ :=
  100*(100*((Val.list [sv,gv,dv,xv,yv]).wt+100)+1)

open Classical in
/-- The actual source and alignment/twist target pullbacks, followed by the
state constructor, give the exact original-position query value. -/
theorem itcs_colors_state_query {Pg : Program}
    {f cmp rng pull cb bit state B : ℕ}
    (hf : Pg.funs[f]? = some (itcsColorsStateF cmp rng pull state))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hm : Pg.HasAt pull (mapFuns pull cb)) (hb : Pg.funs[cb]? = some (itcsPullB bit))
    (hbit : Pg.funs[bit]? = some itcsPullF) (hst : Pg.funs[state]? = some itcsStateF)
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B)
    (v : ℕ) (hv : v ≤ B) (a₀ : Perm (Fin L.q)) (t : permitted W R)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (sv : List Val) (hier : Val)
    (hk : sv[0]? = some (.nat k)) (hh : sv[5]? = some hier)
    (hN : sv[9]? = some (.nat S.N)) :
    let M : W → R → Bool := itcsMatrix X v
    let N := fun (w : W) (r : R) => decide (Y.col (a₀ w.val) (a₀ r.val) = v)
    let G := encGroup (hs.map Prod.fst)
    let D := encFun fun i => if e.symm i ∈ rep.Δ then 1 else 0
    let Vx := encFun fun i => itcsQCode (rep.colors M (e.symm i))
    let Vy := encFun fun i => itcsQCode (rep.colors (RectRep.twistMat t N) (e.symm i))
    let inp := Val.list [.list sv,G,D,rcColVal X,rcColVal Y,.nat v,.nat L.q,
      encFun (fun i => rcCellCode (rep.cell (e.symm i))),encPerm a₀,encPerm t.val.val]
    FunDet Pg f inp (itcsQVal e rep M N t hs hier)
      (itcsColorsStateC inp.wt (permK*(L.q+1)^3) (7000*(L.q+1)^3)
        (itcsPullC k L.q B) (itcsPullC k L.q B) (itcsStateC (.list sv) G D Vx Vy)) := by
  dsimp only
  let M : W → R → Bool := itcsMatrix X v
  let N := fun (w : W) (r : R) => decide (Y.col (a₀ w.val) (a₀ r.val) = v)
  let G := encGroup (hs.map Prod.fst)
  let D := encFun fun i => if e.symm i ∈ rep.Δ then 1 else 0
  let Vx := encFun fun i => itcsQCode (rep.colors M (e.symm i))
  let Vy := encFun fun i => itcsQCode (rep.colors (RectRep.twistMat t N) (e.symm i))
  have hx := itcs_pull_prog hm hb hbit X x₀ hX v hv (1:Perm (Fin L.q)) (fun i => rep.cell (e.symm i))
  have hy := itcs_pull_prog hm hb hbit Y y₀ hY v hv (a₀*t.val.val) (fun i => rep.cell (e.symm i))
  have hxp : FunDet Pg pull (.list [.list [rcColVal X,.nat v,.nat L.q,encPerm (1:Perm (Fin L.q))],
      encFun (fun i => rcCellCode (rep.cell (e.symm i)))]) Vx (itcsPullC k L.q B) := by
    simpa only [Vx,M,itcs_source_pull,itcsPullCtx] using hx
  have hyp : FunDet Pg pull (.list [.list [rcColVal Y,.nat v,.nat L.q,encPerm (a₀*t.val.val)],
      encFun (fun i => rcCellCode (rep.cell (e.symm i)))]) Vy (itcsPullC k L.q B) := by
    simpa only [Vy,N,itcs_target_pull,itcsPullCtx] using hy
  have hsval := itcs_state_prog sv G D Vx Vy hier hk hh hN hst
  have rangeId : FunDet Pg rng (.nat L.q) (encPerm (1:Perm (Fin L.q))) (7000*(L.q+1)^3) := by
    simpa only [it_range_one] using range_det hr L.q
  exact itcs_colors_state_prog hf (.list sv) G D (rcColVal X) (rcColVal Y) (.nat v) (.nat L.q)
    (encFun fun i => rcCellCode (rep.cell (e.symm i))) (encPerm a₀) (encPerm t.val.val)
    (encPerm (a₀*t.val.val)) (encPerm (1:Perm (Fin L.q))) Vx Vy
    (itcsQVal e rep M N t hs hier) (compose_spec hc a₀ t.val.val) rangeId hxp hyp hsval

end GI.Impl
