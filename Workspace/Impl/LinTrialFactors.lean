import Workspace.Impl.LinTrialFactor
import Workspace.Impl.LinMapSource

/-! Run bounded trial division over the cyclic orders. Repeated orders require
no injectivity assumption on the input encoding. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len)

def linTrialFactorsFuns (b : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linTrialFactorFuns (b + 3)

theorem linTrialFactorsFuns_length (b : ℕ) : (linTrialFactorsFuns b).length = 29 := rfl

structure linTrialFactorsAt (P : Program) (b : ℕ) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  cell : linTrialFactorAt P (b + 3)

theorem linTrialFactorsAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linTrialFactorsFuns b)) : linTrialFactorsAt P b where
  map := h.block 0 rfl
  cell := linTrialFactorAt_of (h.block 3 rfl)

def linTrialFactorsCost (W : ℕ) : ℕ := linMapBudget W (linTrialFactorCost (100 * (W + 1)))

noncomputable def linTrialFactorsVal {d p : ℕ} (m : Fin d → ℕ) : Val :=
  .list ((List.finRange d).map fun i =>
    let e := (linTrialPrimary p (m i) (len (m i))).1
    .list [.nat e, encInt (p ^ e : ℤ)])

set_option maxHeartbeats 1000000 in
theorem linTrialFactors_spec {P : Program} {b p d : ℕ} (h : linTrialFactorsAt P b)
    (m : Fin d → ℕ) (hp : p.Prime) (hm : ∀ i, 0 < m i) :
    FunDet P b (.list [.nat p, linVecVal (fun i => (m i : ℤ))])
      (linTrialFactorsVal (p := p) m)
      (linTrialFactorsCost (Val.list [.nat p, linVecVal (fun i => (m i : ℤ))]).wt) := by
  let a := Val.list [.nat p, linVecVal (fun i => (m i : ℤ))]
  let W := a.wt
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have wm : (linVecVal (fun i => (m i : ℤ))).wt < W := wt_le_wt_list (by simp [a, W])
  have hc (i : Fin d) : FunDet P (b + 3) (.list [.nat p, encInt (m i : ℤ)])
      (.list [.nat (linTrialPrimary p (m i) (len (m i))).1,
        encInt (p ^ (linTrialPrimary p (m i) (len (m i))).1 : ℤ)])
      (linTrialFactorCost (100 * (W + 1))) := by
    have wi := (linVecEntryWt (fun i => (m i : ℤ)) i).trans wm
    have hh := wt_list2_le (.nat p) (encInt (m i : ℤ))
    exact (linTrialFactor_spec h.cell p (m i) hp (hm i)).mono
      (linTrialFactorCost_mono (by omega))
  exact linMapSource_spec h.map (fun i => encInt (m i : ℤ))
    (fun i => .list [.nat (linTrialPrimary p (m i) (len (m i))).1,
      encInt (p ^ (linTrialPrimary p (m i) (len (m i))).1 : ℤ)])
    (.nat p) (List.finRange d) _ (fun i _ => hc i)

theorem linTrialFactorsCost_poly : PBU (fun _ W _ => linTrialFactorsCost W) := by
  unfold linTrialFactorsCost linMapBudget linTrialFactorCost linTrialExponentCost
    linTrialExponentBudget linTrialExponentArg linTrialFactorPower linTrialFactorEncode
    linNatPowerCost linTrialPrimaryCost linIntCodecCost
  norm_poly

end GI.Impl
