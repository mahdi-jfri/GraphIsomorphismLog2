module

public import Workspace.Impl.LinPrimePassSuccess

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linPrimePassPrepareArgE : Expr :=
  .snoc (mk4 (arg 0) (arg 1)
    (.get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0)) (arg 3)) (arg 4)

set_option maxHeartbeats 1000000 in
theorem linPrimePassPrepareArg_spec {P : Program} {n d : ℕ}
    (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) (p : ℕ) :
    let a := linPrimePrepareInputVal gs m ρ c x r p
    Det P [a] linPrimePassPrepareArgE (linPrimePrepareInputVal gs m ρ c x 1 p)
      (100000 * (a.wt + 1)) := by
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let orders := linVecVal (fun i => (m i : ℤ))
  let a := linPrimePrepareInputVal gs m ρ c x r p
  let W := a.wt
  have darg (j : ℕ) {v : Val} (hj : ([ctx, point, encPerm r, .nat p, orders] : List Val)[j]? = some v) :=
    Det.arg' (P := P) (vs := [ctx, point, encPerm r, .nat p, orders]) (rest := []) (j := j) hj
  have dc := darg 0 rfl
  have dg := Det.get' dc (Det.nat 0) rfl
  have dl := Det.get' dg (Det.nat 1) rfl
  have di := Det.get' dl (Det.nat 0) rfl
  have dout := Det.snoc (Det.mk4 dc (darg 1 rfl) di (darg 3 rfl)) (darg 4 rfl)
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [a, W, ctx, linPrimePrepareInputVal])
  have wpt : point.wt < W := wt_le_wt_list (by simp [a, W, point, linPrimePrepareInputVal])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal])
  have wo : orders.wt < W := wt_le_wt_list (by simp [a, W, orders, linPrimePrepareInputVal])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have wi : (encPerm (1 : Equiv.Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have w4 := wt_list4_le ctx point (encPerm (1 : Equiv.Perm (Fin n))) (.nat p)
  have w5 := wt_list_snoc_le [ctx, point, encPerm (1 : Equiv.Perm (Fin n)), .nat p] orders
  refine dout.mono ?_
  change _ ≤ 100000 * (W + 1)
  dsimp only [W, a, ctx, point, orders, linPrimePrepareInputVal, linActionContext, encGroup] at *
  simp only [List.map_cons] at *
  omega

end GI.Impl
