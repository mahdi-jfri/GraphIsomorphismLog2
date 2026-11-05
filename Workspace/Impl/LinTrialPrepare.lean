module

public import Workspace.Impl.LinTrialFactors
public import Workspace.Impl.LinPairColumns

@[expose] public section

/-! Prepare the primary exponent vector and signed cyclic-order vector from
positive signed orders. The prime remains an explicit small input. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linTrialPrepareF (collect split : ℕ) : Expr :=
  .letE (.call collect (.var 0)) (.call split (.var 1))

def linTrialPrepareFuns (b : ℕ) : List Expr :=
  [linTrialPrepareF (b + 1) (b + 30)] ++
    linTrialFactorsFuns (b + 1) ++ linPairColumnsFuns (b + 30)

theorem linTrialPrepareFuns_length (b : ℕ) : (linTrialPrepareFuns b).length = 35 := rfl

structure linTrialPrepareAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linTrialPrepareF (b + 1) (b + 30))
  collect : linTrialFactorsAt P (b + 1)
  split : linPairColumnsAt P (b + 30)

theorem linTrialPrepareAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linTrialPrepareFuns b)) : linTrialPrepareAt P b where
  entry := (h.block (gs := [linTrialPrepareF (b + 1) (b + 30)]) 0 rfl).single
  collect := linTrialFactorsAt_of (h.block 1 rfl)
  split := linPairColumnsAt_of (h.block 30 rfl)

def linTrialPrepareSplitBudget (W : ℕ) : ℕ := linPairColumnsCost (linTrialFactorsCost W)
def linTrialPrepareCost (W : ℕ) : ℕ :=
  10000 * (W + linTrialFactorsCost W + linTrialPrepareSplitBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 6000 in
theorem linTrialPrepare_spec {P : Program} {b d p : ℕ} (h : linTrialPrepareAt P b)
    (m : Fin d → ℕ) (hp : p.Prime) (hm : ∀ i, 0 < m i) :
    let D := linTrialPrimaryData m p hp hm
    let a := Val.list [.nat p, linVecVal (fun i => (m i : ℤ))]
    FunDet P b a (.list [encFun D.exponent,
      linVecVal (fun i => (linPrimaryOrders p D.exponent i : ℤ))])
      (linTrialPrepareCost a.wt) := by
  let D := linTrialPrimaryData m p hp hm
  let a := Val.list [.nat p, linVecVal (fun i => (m i : ℤ))]
  let W := a.wt
  let xs : List (Val × Val) := (List.finRange d).map fun i =>
    (.nat (D.exponent i), encInt (linPrimaryOrders p D.exponent i : ℤ))
  have hval : linPairColumnsVal xs = linTrialFactorsVal (p := p) m := by
    simp only [linPairColumnsVal, xs, List.map_map, Function.comp_def,
      linTrialFactorsVal, D, linTrialPrimaryData, linPrimaryOrders, Int.natCast_pow]
  have hs := linTrialFactors_spec h.collect m hp hm
  have hw : (linPairColumnsVal xs).wt ≤ linTrialFactorsCost W := by
    rw [hval]
    exact hs.wt_lt.le
  have ht := (linPairColumns_spec h.split xs).mono (linPairColumnsCost_mono hw)
  have heq : Val.list [Val.list (xs.map Prod.fst), Val.list (xs.map Prod.snd)] =
      .list [encFun D.exponent, linVecVal (fun i => (linPrimaryOrders p D.exponent i : ℤ))] := by
    simp only [xs, List.map_map, Function.comp_def, encFun, linVecVal]
  rw [heq, hval] at ht
  have dcollect := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hs
  have dsplit := Det.call (Det.var' (P := P) (env := [a, linTrialFactorsVal (p := p) m]) (i := 1) rfl) ht
  rw [hval] at hw
  have wo := ht.wt_lt.le
  apply FunDet.intro h.entry
  refine (Det.letE dcollect dsplit).mono ?_
  change _ ≤ linTrialPrepareCost W
  unfold linTrialPrepareCost
  dsimp only [W, a, linTrialPrepareSplitBudget] at *
  omega

theorem linTrialPrepareCost_poly : PBU (fun _ W _ => linTrialPrepareCost W) := by
  unfold linTrialPrepareCost linTrialPrepareSplitBudget linPairColumnsCost linPairColumnsBudget
    linTrialFactorsCost linMapBudget linTrialFactorCost linTrialExponentCost
    linTrialExponentBudget linTrialExponentArg linTrialFactorPower linTrialFactorEncode
    linNatPowerCost linTrialPrimaryCost linIntCodecCost
  norm_poly

end GI.Impl
