import Workspace.Impl.AggItemCiSojProcess
import Workspace.Impl.AggItemCiSojProcessW

/-! # Processing a rectangle answer with a bound on actual input weight -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens NormalizedFactor)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Every size premise of the answer projector follows from its actual encoded
input. The returned group is the full projected source subgroup. -/
theorem itcs_process_local (hfac : NormalizedFactor)
    {Pg : Program} {f pi gm mp cmp sb sp jfac : ℕ}
    (hf : Pg.funs[f]? = some (itcsProjectF pi gm cmp))
    (hpi : Pg.funs[pi]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hgm : Pg.funs[gm]? = some (itcsGroupMapF mp)) (hm : Pg.HasAt mp (mapFuns mp pi))
    (hc : Pg.HasAt cmp (composeFuns cmp))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (g : rep.H) (t : permitted W R) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    let ts := (itcsLiftGens e rep M gs hgs).map (fun a => (itcsRepMap rep a).val.val)
    let inp := Val.list [liftLabCtx L.q k (hs.map Prod.swap),
      .list [encPerm (toFin e g.val), encGroup gs], encPerm t.val.val]
    FunDet Pg f inp (.list [encPerm (t * itcsRepMap rep g).val.val, encGroup ts])
      (itcsProcessC (normalizedFactorPrim hfac) inp.wt) := by
  dsimp only
  let inp := Val.list [liftLabCtx L.q k (hs.map Prod.swap),
    .list [encPerm (toFin e g.val),encGroup gs],encPerm t.val.val]
  have hw := itcs_process_input_sizes hs (toFin e g.val) gs t.val.val
  change _ ≤ inp.wt ∧ _ ≤ inp.wt ∧ k ≤ inp.wt ∧ L.q ≤ inp.wt ∧
    hs.length ≤ inp.wt ∧ gs.length ≤ inp.wt at hw
  have hu : inp.wt ≤ itcsProjU inp.wt := (Nat.le_add_right _ 20).trans (itcs_proj_u_ge _)
  have ho := itcs_group_envelope
    ((itcsLiftGens e rep M gs hgs).map (fun a => (itcsRepMap rep a).val.val))
    (show ((itcsLiftGens e rep M gs hgs).map (fun a => (itcsRepMap rep a).val.val)).length ≤ inp.wt from by
      simpa only [List.length_map,itcsLiftGens,List.length_attach] using hw.2.2.2.2.2)
    hw.2.2.2.1
  exact itcs_process_some hfac hf hpi hsh hsp hj hgm hm hc e rep M hs hhs g t gs hgs
    (hw.2.2.1.trans hu) (hw.2.2.2.1.trans hu) (hw.2.2.2.2.1.trans hu)
    (hw.2.2.2.2.2.trans hu) (hw.1.trans hu) (hw.2.1.trans hu) ho

end GI.Impl
