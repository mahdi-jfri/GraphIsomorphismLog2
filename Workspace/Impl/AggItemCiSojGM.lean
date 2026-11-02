import Workspace.Impl.AggItemCiSojPG
import Workspace.Impl.AggItemCiSojRP

/-!
# The actual map of canonical answer generators

The encoded group includes its leading identity. Project that list through the
same normalized-factor program as the representative. The leading identity stays
identity, and the remaining generators generate the full projected source group.
-/

set_option maxHeartbeats 400000

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens NormalizedFactor)

/-- The permutation-list field of a group encoding, including its leading identity. -/
def itcsGenList {n : ℕ} (gs : List (Perm (Fin n))) : Val :=
  .list ((1 :: gs).map encPerm)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Taking positions of the unique physical lifts returns the original generator list. -/
theorem itcs_lift_gens_toFin (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M : W → R → Bool) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    (itcsLiftGens e rep M gs hgs).map (fun g => toFin e g.val) = gs := by
  have hh := congrArg (List.map (toFin e)) (itcs_lift_gens_val e rep M gs hgs)
  simp only [List.map_map, Function.comp_def] at hh
  change (itcsLiftGens e rep M gs hgs).map (fun g => toFin e g.val) =
    gs.map (fun x => toFin e ((toFin e).symm x)) at hh
  rw [show (fun x => toFin e ((toFin e).symm x)) = id from
    funext ((toFin e).apply_symm_apply), List.map_id] at hh
  exact hh

/-- The program's generator-map cost, before substituting round bounds. -/
noncomputable def itcsGenMapC (pf : Prim) (k q l n : ℕ) (ctx gv out : Val) : ℕ :=
  (n + 1) * liftLabCost pf (l + q + k + 2) +
    mapK * (n + 2) * ((Val.list [ctx, gv]).wt + out.wt + 1)

/-- Map all canonical generators through the rectangle's stored graph.
Membership of every mapped element is supplied by the proved full source group equality. -/
theorem itcs_gen_map (hfac : NormalizedFactor) {Pg : Program} {mp f sb sp jfac : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f))
    (hf : Pg.funs[f]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (gs : List (Perm (Fin k))) (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    let out := itcsGenList ((itcsLiftGens e rep M gs hgs).map (fun g => (itcsRepMap rep g).val.val))
    FunDet Pg mp (.list [liftLabCtx L.q k (hs.map Prod.swap), itcsGenList gs]) out
      (itcsGenMapC (normalizedFactorPrim hfac) k L.q hs.length gs.length
        (liftLabCtx L.q k (hs.map Prod.swap)) (itcsGenList gs) out) := by
  dsimp only
  let ls := itcsLiftGens e rep M gs hgs
  let inp : rep.H → Val := fun g => encPerm (toFin e g.val)
  let out : rep.H → Val := fun g => encPerm (itcsRepMap rep g).val.val
  have hmap := mapList_spec hm (1 :: ls) inp out
    (c := liftLabCtx L.q k (hs.map Prod.swap))
    (B := liftLabCost (normalizedFactorPrim hfac) (hs.length + L.q + k + 2))
    (fun a _ b _ hh => by
      apply congrArg out
      apply Subtype.ext
      exact (toFin e).injective (encPerm_injective hh))
    (fun g _ => itcs_rep_pi_prog hfac hf hsh hsp hj e rep hs hhs g)
  have hi : (1 :: ls).map inp = (1 :: gs).map encPerm := by
    simp only [List.map_cons, inp, OneMemClass.coe_one, map_one, List.cons.injEq, true_and]
    rw [show ls.map (fun g => encPerm (toFin e g.val)) =
      (ls.map (fun g => toFin e g.val)).map encPerm by rw [List.map_map]; rfl]
    rw [itcs_lift_gens_toFin]
  have ho : (1 :: ls).map out =
      (1 :: ls.map (fun g => (itcsRepMap rep g).val.val)).map encPerm := by
    simp only [List.map_cons, out, map_one, OneMemClass.coe_one, List.map_map]
    rfl
  rw [hi, ho] at hmap
  have hl : ls.length = gs.length := by simp only [ls, itcsLiftGens, List.length_map, List.length_attach]
  simp only [List.length_cons, hl] at hmap
  change FunDet Pg mp (.list [liftLabCtx L.q k (hs.map Prod.swap), itcsGenList gs])
    (itcsGenList (ls.map (fun g => (itcsRepMap rep g).val.val)))
    ((gs.length + 1) * liftLabCost (normalizedFactorPrim hfac) (hs.length + L.q + k + 2) +
      mapK * (gs.length + 1 + 1) *
        ((Val.list [liftLabCtx L.q k (hs.map Prod.swap), itcsGenList gs]).wt +
          (itcsGenList (ls.map (fun g => (itcsRepMap rep g).val.val))).wt + 1)) at hmap
  simpa only [itcsGenMapC, Nat.add_assoc] using hmap

end GI.Impl
