import Workspace.Impl.AggItemCiSojAskProg
import Workspace.Impl.AggItemCiSojFrame

/-! # The initial-request byte program produces the retained semantic frame -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

open Classical in
/-- Physical-data and exact query-state constructors give the actual initial
request for a frame. Every projection and twist is taken from the stored
representation bytes. -/
theorem itcs_ask_frame {Pg : Program} {f data colors Cd Cq : ℕ}
    (hf : Pg.funs[f]? = some (itcsAskF data colors)) (F : itcsQFrame e S L)
    (sv v side xt yt : Val) (xc yc : List Val)
    (hx : xc[0]?=some xt) (hy : yc[0]?=some yt)
    (hd : FunDet Pg data (.list [sv,.nat L.q,.list (F.hs.map pairV),
      encFun fun i => rcCellCode (F.rep.cell (e.symm i))])
      (.list [encGroup (F.hs.map Prod.fst),encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),
        liftLabCtx L.q k (F.hs.map Prod.swap)]) Cd)
    (hq : ∀ t : permitted F.W F.R,
      FunDet Pg colors (.list [sv,encGroup (F.hs.map Prod.fst),
        encFun (fun i => if e.symm i∈F.rep.Δ then 1 else 0),xt,yt,v,.nat L.q,
        encFun (fun i => rcCellCode (F.rep.cell (e.symm i))),encPerm F.a₀.val,encPerm t.val.val])
        (F.query t) Cq) :
    let inp := Val.list [sv,.nat L.q,.list xc,.list yc,v,encPerm F.a₀.val,
      .list ((itciMs (itcsFixColor F.W) (itciOt (itcsFixColor F.W))).map encPerm),
      rcRepVal e F.rep F.hs,encPerm (1:Perm (Fin L.q)),side]
    FunDet Pg f inp (itcsAskV (F.query 1) F.payload (.list F.pending))
      (itcsAskC inp.wt Cd Cq Cq) := by
  let G := encGroup (F.hs.map Prod.fst)
  let D := encFun fun i => if e.symm i∈F.rep.Δ then 1 else 0
  let LC := liftLabCtx L.q k (F.hs.map Prod.swap)
  let cells := encFun fun i => rcCellCode (F.rep.cell (e.symm i))
  let fix := Val.list ((itciMs (itcsFixColor F.W) (itciOt (itcsFixColor F.W))).map encPerm)
  cases ht : F.rep.twist with
  | none =>
    have hh := itcs_ask_prog (C₀:=Cq) (C₁:=Cq) hf sv (.nat L.q) v (encPerm F.a₀.val) fix (.list (F.hs.map pairV)) cells
      (encPerm (1:Perm (Fin L.q))) side xt yt G D LC (F.query 1) (.list []) xc yc none hx hy hd (hq 1)
      (fun t ht => by cases ht)
    simpa only [rcRepVal,ht,Option.toList_none,Option.map_none,itcsQFrame.payload,itcsQFrame.pending,
      itcsTwists,List.map_nil,List.map_cons,Option.toList_none,fix,G,D,LC,cells] using hh
  | some t =>
    have hqt (t' : Val) (he : some (encPerm t.val.val)=some t') :
        FunDet Pg colors (.list [sv,G,D,xt,yt,v,.nat L.q,cells,encPerm F.a₀.val,t']) (F.query t) Cq := by
      have he' : t'=encPerm t.val.val := (Option.some.inj he).symm
      subst t'
      exact hq t
    have hh := itcs_ask_prog (C₀:=Cq) (C₁:=Cq) hf sv (.nat L.q) v (encPerm F.a₀.val) fix (.list (F.hs.map pairV)) cells
      (encPerm (1:Perm (Fin L.q))) side xt yt G D LC (F.query 1) (F.query t) xc yc
      (some (encPerm t.val.val)) hx hy hd (hq 1) hqt
    simpa only [rcRepVal,ht,Option.toList_some,Option.map_some,itcsQFrame.payload,itcsQFrame.pending,
      itcsTwists,List.map_nil,List.map_cons,fix,G,D,LC,cells] using hh

end GI.Impl
