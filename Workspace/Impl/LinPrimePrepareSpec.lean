module

public import Workspace.Impl.LinPrimePrepareCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimeModuli_snoc {d : ℕ} (m : Fin d → ℕ) :
    linVecVal (linFiniteModuli m) =
      .list (((List.finRange d).map fun i => encInt (m i : ℤ)) ++ [encInt 0]) := by
  exact congrArg Val.list (linExtend_value encInt (fun i => (m i : ℤ)) 0)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem linPrimePrepare_spec {P : Program} {b n d p : ℕ} (h : linPrimePrepareAt P b)
    (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ) (hp : p.Prime) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (x : linFiniteVec m) (r : Equiv.Perm (Fin n)) :
    let D := linTrialPrimaryData m p hp hm
    let a := linPrimePrepareInputVal gs m ρ c x r p
    FunDet P b a (linPrimaryLoopInputVal gs D.exponent (linPrimeAction D hm ρ)
      (fun g => linPrimeProjection D (c g)) (linPrimeProjection D x) r)
      (linPrimePrepareCost a.wt) := by
  let D := linTrialPrimaryData m p hp hm
  let q := linPrimaryOrders p D.exponent
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let a := linPrimePrepareInputVal gs m ρ c x r p
  let W := a.wt
  let factors := Val.list [encFun D.exponent, linVecVal (fun i => (q i : ℤ))]
  let orders := linVecVal (linFiniteModuli q)
  let newctx := linActionContext gs q (linPrimeAction D hm ρ) (fun g => linPrimeProjection D (c g))
  let newpoint := linFinitePointVal q (linPrimeProjection D x)
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal, ctx])
  have wpoint : point.wt < W := wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal, point])
  have wr : (encPerm r).wt < W := wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal])
  have wm : (linVecVal (fun i => (m i : ℤ))).wt < W :=
    wt_le_wt_list (by simp [a, W, linPrimePrepareInputVal])
  have wtarg : (Val.list [.nat p, linVecVal (fun i => (m i : ℤ))]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat p) (linVecVal (fun i => (m i : ℤ)))
    omega
  have ht := (linTrialPrepare_spec h.trial m hp hm).mono (linTrialPrepareCost_mono wtarg)
  have wfactors : factors.wt ≤ linPrimePrepareTrialBudget W := ht.wt_lt.le
  have wbase : (linVecVal (fun i => (q i : ℤ))).wt < factors.wt := wt_le_wt_list (by simp [factors])
  have wν : (encFun D.exponent).wt < factors.wt := wt_le_wt_list (by simp [factors])
  have worders : orders.wt ≤ 100 * (linPrimePrepareTrialBudget W + 1) := by
    have hh := wt_list_snoc_le ((List.finRange d).map fun i => encInt (q i : ℤ)) (encInt 0)
    have hz : (encInt 0).wt = 15 := rfl
    change (Val.list ((List.finRange d).map fun i => encInt (q i : ℤ))).wt < factors.wt at wbase
    dsimp only [orders]
    rw [linPrimeModuli_snoc]
    omega
  have wcarg : (Val.list [orders, ctx]).wt ≤ linPrimePrepareSubArg W := by
    have hh := wt_list2_le orders ctx
    unfold linPrimePrepareSubArg
    omega
  have wparg : (Val.list [point, orders]).wt ≤ linPrimePrepareSubArg W := by
    have hh := wt_list2_le point orders
    unfold linPrimePrepareSubArg
    omega
  have hc := (linPrimeContext_spec h.context gs D hm ρ c).mono (linPrimeContextCost_mono wcarg)
  have hpoint := (linPrimePoint_spec h.point D hp hm x).mono (linPrimePointCost_mono wparg)
  have wnctx : newctx.wt ≤ linPrimePrepareContextBudget W := hc.wt_lt.le
  have wnpoint : newpoint.wt ≤ linPrimePreparePointBudget W := hpoint.wt_lt.le
  have darg (j : ℕ) (v : Val) (hj : [ctx, point, encPerm r, .nat p, linVecVal (fun i => (m i : ℤ))][j]? = some v)
      (rest : List Val) := Det.arg' (P := P)
        (vs := [ctx, point, encPerm r, .nat p, linVecVal (fun i => (m i : ℤ))]) (rest := rest) hj
  have dt := Det.call (Det.mk2 (darg 3 (.nat p) rfl [])
    (darg 4 (linVecVal (fun i => (m i : ℤ))) rfl [])) ht
  have dbase := Det.get' (Det.var' (P := P) (env := [a, factors]) (i := 1) rfl) (Det.nat 1) rfl
  have dz : Det P [a, factors] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have dorders := Det.snoc dbase dz
  rw [← linPrimeModuli_snoc q] at dorders
  have dc := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, factors, orders]) (i := 2) rfl)
    (darg 0 ctx rfl [factors, orders])) hc
  have dp := Det.call (Det.mk2 (darg 1 point rfl [factors, orders, newctx])
    (Det.var' (P := P) (env := [a, factors, orders, newctx]) (i := 2) rfl)) hpoint
  have dν := Det.get' (Det.var' (P := P) (env := [a, factors, orders, newctx, newpoint])
    (i := 1) rfl) (Det.nat 0) rfl
  have dout := Det.snoc (Det.mk4
    (Det.var' (P := P) (env := [a, factors, orders, newctx, newpoint]) (i := 3) rfl)
    (Det.var' (P := P) (env := [a, factors, orders, newctx, newpoint]) (i := 4) rfl)
    (darg 2 (encPerm r) rfl [factors, orders, newctx, newpoint])
    (darg 3 (.nat p) rfl [factors, orders, newctx, newpoint])) dν
  apply FunDet.intro h.entry
  refine (Det.letE dt (Det.letE dorders (Det.letE dc (Det.letE dp dout)))).mono ?_
  have wo4 := wt_list4_le newctx newpoint (encPerm r) (.nat p)
  have wo5 := wt_list_snoc_le [newctx, newpoint, encPerm r, .nat p] (encFun D.exponent)
  have wi := wt_list2_le (.nat p) (linVecVal (fun i => (m i : ℤ)))
  have wci := wt_list2_le orders ctx
  have wpi := wt_list2_le point orders
  change _ ≤ linPrimePrepareCost W
  unfold linPrimePrepareCost
  dsimp only [W, a, ctx, point, factors, orders, newctx, newpoint, D, q,
    linPrimePrepareTrialBudget, linPrimePrepareContextBudget, linPrimePreparePointBudget,
    linPrimePrepareInputVal, linPrimaryLoopInputVal] at *
  omega

end GI.Impl
