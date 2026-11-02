import Workspace.Impl.AggItemCiSojIW
import Workspace.Impl.AggItemCiSojProjB

/-! # Weight bounds supplied by the actual answer-processing input -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

/-- A group of bounded degree with a bounded generator list fits the local
quartic envelope. -/
theorem itcs_group_envelope {q W : ℕ} (gs : List (Perm (Fin q)))
    (hn : gs.length ≤ W) (hq : q ≤ W) : (encGroup gs).wt ≤ itcsProjU W := by
  have hp : (gs.length+2)*(q+1) ≤ (W+20)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hs := Nat.pow_le_pow_left hp 2
  have he : ((W+20)^2)^2=(W+20)^4 := by ring
  rw [he] at hs
  exact (wt_encGroup_le gs).trans ((Nat.mul_le_mul_left 40 hs).trans
    (Nat.mul_le_mul_right _ (by decide : 40≤1000)))

/-- The stored lift context and answer bound every degree and generator count
used by the projection programs. -/
theorem itcs_process_input_sizes {k q : ℕ}
    (hs : List (Perm (Fin k) × Perm (Fin q)))
    (x : Perm (Fin k)) (gs : List (Perm (Fin k))) (t : Perm (Fin q)) :
    let ctx := liftLabCtx q k (hs.map Prod.swap)
    let inp := Val.list [ctx, .list [encPerm x,encGroup gs],encPerm t]
    ctx.wt ≤ inp.wt ∧ (encGroup gs).wt ≤ inp.wt ∧
      k ≤ inp.wt ∧ q ≤ inp.wt ∧ hs.length ≤ inp.wt ∧ gs.length ≤ inp.wt := by
  dsimp only
  let ctx := liftLabCtx q k (hs.map Prod.swap)
  let ans := Val.list [encPerm x,encGroup gs]
  let inp := Val.list [ctx,ans,encPerm t]
  have hc : ctx.wt ≤ inp.wt := st_wt_mem (by simp only [List.mem_cons_self,inp])
  have ha : ans.wt ≤ inp.wt := st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hg : (encGroup gs).wt ≤ inp.wt :=
    (st_wt_mem (show encGroup gs∈[encPerm x,encGroup gs] from by simp)).trans ha
  have hl := itcs_lift_sizes (hs.map Prod.swap)
  simp only [List.length_map] at hl
  exact ⟨hc,hg,hl.2.1.trans hc,hl.1.trans hc,hl.2.2.trans hc,
    (itcs_group_length gs).trans hg⟩

end GI.Impl
