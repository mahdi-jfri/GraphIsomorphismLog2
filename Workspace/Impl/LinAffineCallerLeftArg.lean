import Workspace.Impl.LinAffineCallerPrep

namespace GI.Impl
open GI.Cited GI.Lang

def linAffineCallerLeftArgE : Expr :=
  mk2 (.get (.get (.var 2) (.nat 0)) (.nat 0)) (.get (.var 2) (.nat 2))

set_option maxHeartbeats 1000000 in
theorem linAffineCallerLeftArg_spec {P : Program} {n : ℕ}
    (a prep table ident point : Val) (gs : List (Equiv.Perm (Fin n))) (r : Equiv.Perm (Fin n)) :
    let ans := Val.list [.list [encGroup gs, table, ident], point, encPerm r]
    Det P [a, prep, ans] linAffineCallerLeftArgE (.list [encGroup gs, encPerm r])
      (100000 * (ans.wt + 1)) := by
  let ctx := Val.list [encGroup gs, table, ident]
  let ans := Val.list [ctx, point, encPerm r]
  have da := Det.var' (P := P) (env := [a, prep, ans]) (i := 2) rfl
  have dc := Det.get' da (Det.nat 0) rfl
  have dg := Det.get' dc (Det.nat 0) rfl
  have dr := Det.get' da (Det.nat 2) rfl
  have dd := Det.mk2 dg dr
  have wc : ctx.wt < ans.wt := wt_le_wt_list (by simp [ans])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wr : (encPerm r).wt < ans.wt := wt_le_wt_list (by simp [ans])
  have wo := wt_list2_le (encGroup gs) (encPerm r)
  refine dd.mono ?_
  dsimp only [ans, ctx] at *
  omega

theorem linAffineLeftCost_mono {W V : ℕ} (h : W ≤ V) : linAffineLeftCost W ≤ linAffineLeftCost V := by
  simp only [linAffineLeftCost, linAffineLeftInvBudget, linAffineLeftTailBudget,
    linAffineLeftMapBudget, linAffineLeftMapArg, linAffineLeftGroupBudget, linMapBudget, linConjugateCellCost]
  gcongr

end GI.Impl
