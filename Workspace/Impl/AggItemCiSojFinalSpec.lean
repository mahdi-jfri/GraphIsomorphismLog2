module

public import Workspace.Impl.AggItemCiSojFinalSome
public import Workspace.Impl.AggItemCiSojRowsSpec

@[expose] public section

/-! # The full proved canonical rectangle-answer finalizer contract -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- The actual full finalizer computes exactly the model's whole rectangle-query
item from all canonical answers in occurrence order, with local polynomial cost. -/
def itcsFinalSpec (Pg : Program) (f : ℕ) (pf : Prim) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S)
    (W R : Finset (Fin L.q)) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (hs : List (Perm (Fin k) × Perm (Fin L.q))),
    PairGens e L rep.H hs → ∀ answers : List Val,
      List.Forall₂ (fun t u => AnsC e u (rep.state M N t).answer) (itcsTwists rep) answers →
      let inp := Val.list [.list [.nat L.q,encPerm a₀.val,
        .list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm),
        liftLabCtx L.q k (hs.map Prod.swap),
        .list ((itcsTwists rep).map fun t => encPerm t.val.val)],.list answers]
      ∃ os, FunDet Pg f inp (itcsResV (itciOV os)) (itcsFinalC pf inp.wt) ∧
        ItSOut e L (AuxItem.query (rep.queries M N a₀) (leftGroup M)).script.evalExact [] os

/-- The installed actual filter, first-field map, full-group constructor and
overcoset mapper prove the full finalizer contract. The row-builder hypothesis
is discharged by `itcs_rows_spec`, including all normalized-factor preconditions. -/
theorem itcs_final_spec {Pg : Program} {f rf flt ne fm fb gb inv mp cmp app ovs ov : ℕ}
    (pf : Prim) (hrows : itcsRowsSpec Pg rf pf)
    (hf : Pg.funs[f]? = some (itcsFinishF rf flt fm gb ovs))
    (hflt : Pg.HasAt flt (filterFuns flt ne)) (hne : Pg.funs[ne]? = some itcsRowNE)
    (hfm : Pg.HasAt fm (mapFuns fm fb)) (hfb : Pg.funs[fb]? = some krFstF)
    (hgb : Pg.funs[gb]? = some (itcsGroupBuildF inv mp app))
    (hi : Pg.HasAt inv (invFuns inv)) (hm : Pg.HasAt mp (mapFuns mp cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (ha : Pg.HasAt app (appendFuns app))
    (ho : Pg.HasAt ovs (mapFuns ovs ov)) (hov : Pg.funs[ov]? = some (itcsOverF cmp)) :
    itcsFinalSpec Pg f pf := by
  intro Ω C k e S L W R rep M N a₀ hs hhs answers hcanon
  let ctx := liftLabCtx L.q k (hs.map Prod.swap)
  let twists := Val.list ((itcsTwists rep).map fun t => encPerm t.val.val)
  let fix := Val.list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm)
  let inp := Val.list [.list [.nat L.q,encPerm a₀.val,fix,ctx,twists],.list answers]
  obtain ⟨rows,horder,hvalid,hr⟩ := hrows e S L W R rep M N hs hhs (.nat L.q) (encPerm a₀.val) fix answers hcanon
  have hModel : itcsRowsModel rep M N a₀ rows =
      (AuxItem.query (rep.queries M N a₀) (leftGroup M)).script.evalExact := by
    rw [itcs_query_seq_item,itcs_query_seq_eval]
    exact itcs_rows_model_of_order rep M N a₀ rows (itcsTwists rep) horder
  rw [←hModel]
  cases he : itcsNonemptyRows rep rows with
  | nil =>
    exact ⟨[],itcs_finalize_none hf hflt hne pf e rep M N a₀ rows hvalid inp hr (le_refl _) he⟩
  | cons p tail =>
    rcases p with ⟨p₀,sg₀⟩
    exact itcs_finalize_some hf hflt hne hfm hfb hgb hi hm hc ha ho hov pf e rep M N a₀ rows
      horder hvalid p₀ sg₀ tail he ctx twists (.list answers) hr (le_refl _)

end GI.Impl
