module

public import Workspace.Impl.LinMixedBounds

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linMixedPassArgE : Expr :=
  .snoc (mk4 (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1))
    (.get (arg 2) (.nat 2)) (.arith .add (arg 1) (.nat 1))) (.get (arg 0) (.nat 3))

set_option maxHeartbeats 1000000 in
theorem linMixedPassArg_spec {P : Program} (v1 v2 v3 orders w1 w2 w3 : Val) (j : ℕ) :
    let orig := Val.list [v1, v2, v3, orders]
    let state := Val.list [w1, w2, w3]
    let a := Val.list [orig, .nat j, state]
    Det P [a] linMixedPassArgE (.list [w1, w2, w3, .nat (j + 1), orders])
      (100000 * (a.wt + j + 1)) := by
  let orig := Val.list [v1, v2, v3, orders]
  let state := Val.list [w1, w2, w3]
  let a := Val.list [orig, .nat j, state]
  let W := a.wt
  have dor := Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 0) rfl
  have dst := Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 2) rfl
  have dj := Det.arg' (P := P) (vs := [orig, .nat j, state]) (rest := []) (j := 1) rfl
  have dw1 := Det.get' dst (Det.nat 0) rfl
  have dw2 := Det.get' dst (Det.nat 1) rfl
  have dw3 := Det.get' dst (Det.nat 2) rfl
  have dp := Det.arith (op := .add) dj (Det.nat 1)
  have dm := Det.get' dor (Det.nat 3) rfl
  have dd := Det.snoc (Det.mk4 dw1 dw2 dw3 dp) dm
  have wo : orig.wt < W := wt_le_wt_list (by simp [a, W])
  have ws : state.wt < W := wt_le_wt_list (by simp [a, W])
  have wm : orders.wt < orig.wt := wt_le_wt_list (by simp [orig])
  have w1h : w1.wt < state.wt := wt_le_wt_list (by simp [state])
  have w2h : w2.wt < state.wt := wt_le_wt_list (by simp [state])
  have w3h : w3.wt < state.wt := wt_le_wt_list (by simp [state])
  have wj := wt_nat_le j
  have wp := wt_nat_le (j + 1)
  have w4 := wt_list4_le w1 w2 w3 (.nat (j + 1))
  have w5 := wt_list_snoc_le [w1, w2, w3, .nat (j + 1)] orders
  simp only [GI.Machine.BinOp.eval_add] at dd
  refine dd.mono ?_
  dsimp only [a, W, orig, state] at *
  omega

def linMixedInitBudget (W : ℕ) : ℕ := 100000 * (W + 1)

set_option maxHeartbeats 1000000 in
theorem linMixedLoop_count_det {P : Program} {n d : ℕ}
    (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) :
    let a := linMixedLoopInputVal gs m ρ c x r
    Det P [a] (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat n) (linMixedInitBudget a.wt) := by
  let ctx := linActionContext gs m ρ c
  let a := linMixedLoopInputVal gs m ρ c x r
  have dc := Det.arg' (P := P) (vs := [ctx, linFinitePointVal m x, encPerm r,
    linVecVal (fun i => (m i : ℤ))]) (rest := []) (j := 0) rfl
  have dg := Det.get' dc (Det.nat 0) rfl
  have dn := Det.get' dg (Det.nat 0) rfl
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp [a, ctx, linMixedLoopInputVal])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wn := wt_nat_le n
  have hn := (linMixedLoop_source_bounds gs m ρ c x r).1
  refine dn.mono ?_
  unfold linMixedInitBudget
  dsimp only [a, ctx, linMixedLoopInputVal] at *
  omega

set_option maxHeartbeats 1000000 in
theorem linMixedLoop_start_det {P : Program} (v1 v2 v3 orders : Val) :
    let a := Val.list [v1, v2, v3, orders]
    Det P [a] (mk3 (arg 0) (arg 1) (arg 2)) (.list [v1, v2, v3]) (linMixedInitBudget a.wt) := by
  let a := Val.list [v1, v2, v3, orders]
  have d1 := Det.arg' (P := P) (vs := [v1, v2, v3, orders]) (rest := []) (j := 0) rfl
  have d2 := Det.arg' (P := P) (vs := [v1, v2, v3, orders]) (rest := []) (j := 1) rfl
  have d3 := Det.arg' (P := P) (vs := [v1, v2, v3, orders]) (rest := []) (j := 2) rfl
  have dd := Det.mk3 d1 d2 d3
  have hw : (Val.list [v1, v2, v3]).wt ≤ a.wt := wt_list_mono ⟨[orders], rfl⟩
  refine dd.mono ?_
  unfold linMixedInitBudget
  dsimp only [a] at *
  omega

end GI.Impl
