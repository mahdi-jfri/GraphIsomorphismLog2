module

public import Workspace.Impl.AggItemCiSojQueryWt

@[expose] public section

/-! # The uniform physical-query cost from paid representation and data bytes -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The exact color-state program has one bound for both recorded query
occurrences. All encoded-argument and state-constructor weight premises are
proved from the paid physical data and paid representation values. -/
theorem itcs_colors_frame_bounded {Pg : Program} {f cmp rng pull cb bit state B n : ℕ}
    (hf : Pg.funs[f]?=some (itcsColorsStateF cmp rng pull state))
    (hcmp : Pg.HasAt cmp (composeFuns cmp)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hm : Pg.HasAt pull (mapFuns pull cb)) (hb : Pg.funs[cb]?=some (itcsPullB bit))
    (hbit : Pg.funs[bit]?=some itcsPullF) (hst : Pg.funs[state]?=some itcsStateF)
    (hc : RectConds P₀ S L W R) (rep : RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B)
    (v : ℕ) (hv : v ≤ B) (a : alternatingGroup (Fin L.q))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (hlen : hs.length ≤ k^2) (sv : List Val) (hier : Val) (hhier : HierValC e hier S.hier)
    (hsvk : sv[0]?=some (.nat k)) (hsvh : sv[5]?=some hier) (hsvN : sv[9]?=some (.nat S.N))
    (hcostCmp : permK*(L.q+1)^3 ≤ n) (hcostRng : 7000*(L.q+1)^3 ≤ n)
    (hcostPull : itcsPullC k L.q B ≤ n)
    (wsv : (Val.list sv).wt ≤ n) (wX : (rcColVal X).wt ≤ n) (wY : (rcColVal Y).wt ≤ n)
    (wv : (Val.nat v).wt ≤ n) (wq : (Val.nat L.q).wt ≤ n) (wp : 4*(L.q+1)^2 ≤ n)
    (wk : k ≤ n) (wrep : (rcRepVal e rep hs).wt ≤ n)
    (wdata : (Val.list [encGroup (hs.map Prod.fst),
      encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),liftLabCtx L.q k (hs.map Prod.swap)]).wt ≤ n) :
    let F := itcsFrameOf hc rep X Y v a hs hhs hlen hier hhier
    ∀ t : permitted W R,
      FunDet Pg f (.list [.list sv,encGroup (hs.map Prod.fst),
        encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),rcColVal X,rcColVal Y,.nat v,.nat L.q,
        encFun (fun i => rcCellCode (rep.cell (e.symm i))),encPerm a.val,encPerm t.val.val])
        (F.query t) (10^9*(10^9*(n+100)+100)) := by
  let F := itcsFrameOf hc rep X Y v a hs hhs hlen hier hhier
  have hn : n ≤ 10^9*(n+100) := by omega
  have hg : (encGroup (hs.map Prod.fst)).wt ≤ n :=
    (st_wt_mem (vs:=[encGroup (hs.map Prod.fst),
      encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),liftLabCtx L.q k (hs.map Prod.swap)])
      (List.mem_cons_self ..)).trans wdata
  have hd : (encFun fun i => if e.symm i∈rep.Δ then 1 else 0).wt ≤ n :=
    (st_wt_mem (vs:=[encGroup (hs.map Prod.fst),
      encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),liftLabCtx L.q k (hs.map Prod.swap)])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wdata
  exact itcs_colors_frame hf hcmp hr hm hb hbit hst hc rep X Y x₀ y₀ hX hY v hv a hs hhs hlen
    sv hier hhier hsvk hsvh hsvN (hcostCmp.trans hn) (hcostRng.trans hn) (hcostPull.trans hn)
    (fun t => itcs_frame_query_input_weight F (.list sv) (rcColVal X) (rcColVal Y) (.nat v)
      wsv wX wY wv wq wp wrep wdata t)
    (fun t => itcs_frame_state_cost F (.list sv) wsv hg hd wk t)

end GI.Impl
