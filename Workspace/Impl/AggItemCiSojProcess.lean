import Workspace.Impl.AggItemCiSojProjB
import Workspace.Impl.AggItemCiSojIW

/-! # Exact processing of a nonempty physical rectangle answer -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens NormalizedFactor)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

set_option maxHeartbeats 200000 in
/-- Project the representative and every source generator through the recorded
rectangle homomorphism, then apply the recorded target twist. -/
theorem itcs_process_some (hfac : NormalizedFactor)
    {Pg : Program} {f pi gm mp cmp sb sp jfac U : ℕ}
    (hf : Pg.funs[f]? = some (itcsProjectF pi gm cmp))
    (hpi : Pg.funs[pi]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hgm : Pg.funs[gm]? = some (itcsGroupMapF mp)) (hm : Pg.HasAt mp (mapFuns mp pi))
    (hc : Pg.HasAt cmp (composeFuns cmp))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (g : rep.H) (t : permitted W R) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M))
    (hk : k ≤ U) (hq : L.q ≤ U) (hl : hs.length ≤ U) (hn : gs.length ≤ U)
    (hctx : (liftLabCtx L.q k (hs.map Prod.swap)).wt ≤ U)
    (hg : (encGroup gs).wt ≤ U)
    (ho : (encGroup ((itcsLiftGens e rep M gs hgs).map
      (fun a => (itcsRepMap rep a).val.val))).wt ≤ U) :
    let ts := (itcsLiftGens e rep M gs hgs).map (fun a => (itcsRepMap rep a).val.val)
    FunDet Pg f (.list [liftLabCtx L.q k (hs.map Prod.swap),
      .list [encPerm (toFin e g.val), encGroup gs], encPerm t.val.val])
      (.list [encPerm (t * itcsRepMap rep g).val.val, encGroup ts])
      (itcsProjectB (normalizedFactorPrim hfac) U) := by
  dsimp only
  let ctx := liftLabCtx L.q k (hs.map Prod.swap)
  let ts := (itcsLiftGens e rep M gs hgs).map (fun a => (itcsRepMap rep a).val.val)
  have wg : (itcsGenList gs).wt ≤ (encGroup gs).wt := st_wt_mem (by simp [encGroup,GI.Cited.encPerms,itcsGenList])
  have wo : (itcsGenList ts).wt ≤ (encGroup ts).wt := st_wt_mem (by simp [encGroup,GI.Cited.encPerms,itcsGenList])
  have mapped := itcs_gen_map hfac hm hpi hsh hsp hj e rep M hs hhs gs hgs
  have mappedB := itcs_gen_map_bound (normalizedFactorPrim hfac) ctx (itcsGenList gs)
    (itcsGenList ts) hk hq hl hn hctx (wg.trans hg) (wo.trans ho)
  have group := itcs_group_map_spec ctx gs ts hgm (mapped.mono mappedB)
  have groupB := itcs_group_map_bound (normalizedFactorPrim hfac) ctx (encGroup gs)
    (itcsGenList ts) hq hctx hg (wo.trans ho) (le_refl _)
  have point := itcs_rep_pi_prog hfac hpi hsh hsp hj e rep hs hhs g
  have pointB : liftLabCost (normalizedFactorPrim hfac) (hs.length + L.q + k + 2) ≤
      itcsLiftB (normalizedFactorPrim hfac) U :=
    itcs_lift_cost_mono _ (by omega)
  have done := itcs_project_spec hf hc (k := k) (q := L.q)
    (vs := [.nat L.q, encGroup ((hs.map Prod.swap).map encPair),
      encGroup ((onePairs (hs.map Prod.swap)).map encPair), pSplitCtx L.q k])
    (by rfl) (toFin e g.val) (itcsRepMap rep g).val.val t.val.val gs ts
    (point.mono pointB) (group.mono groupB)
  have bound := itcs_project_bound (normalizedFactorPrim hfac) ctx (encGroup gs)
    (encGroup ts) hk hq hctx hg ho (le_refl _) (le_refl _)
  exact done.mono bound

end GI.Impl
