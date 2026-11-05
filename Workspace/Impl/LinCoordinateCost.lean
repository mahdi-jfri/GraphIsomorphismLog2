module

public import Workspace.Impl.LinCoordinateCollect
public import Workspace.Impl.LinIntSolverCost

@[expose] public section

/-! Uniform bit-cost bounds for the permutation-input coordinate collector. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

noncomputable def linCoordinatePrepBudget (ho : GroupOrder) (W : ℕ) : ℕ :=
  linCoordinatePrepCost ho (10 * (W + 1)) W W W W

def linCoordinateMemberBudget (W : ℕ) : ℕ := 100 * (W + 1) ^ 3

noncomputable def linCoordinateMemberOutBudget (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  let J := linCoordinateMemberBudget W
  400 * (J ^ linMembershipDegree hm + 1) * (2 * W + J ^ linMembershipDegree hm + 2) + 100

noncomputable def linCoordinateWitnessBudget (ho : GroupOrder) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  let J := linCoordinateMemberBudget W
  let C := linCoordinatePrepBudget ho W
  let MW := linCoordinateMemberOutBudget hm W
  1000 * (C + W + ((linMembershipPrim hm).boundSize J + J + MW + 2) + MW +
    linSlpValueCost (10 * (C + MW + 1)) (J ^ linMembershipDegree hm) W + 1)

noncomputable def linCoordinateRowBudget (ho : GroupOrder) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000 * (10 * (W + 1) + linCoordinatePrepBudget ho W + linCoordinateWitnessBudget ho hm W + 1)

noncomputable def linCoordinateBudget (ho : GroupOrder) (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linCoordinateCollectCost W W (linCoordinateRowBudget ho hm W)

theorem linCoordinatePrepCost_mono (ho : GroupOrder) {W V n m ns ms t s i j : ℕ}
    (hW : W ≤ V) (hn : n ≤ m) (hns : ns ≤ ms) (ht : t ≤ s) (hi : i ≤ j) :
    linCoordinatePrepCost ho W n ns t i ≤ linCoordinatePrepCost ho V m ms s j := by
  simp only [linCoordinatePrepCost, linPrefixOrderCost, linPrefixOrderRatioCost,
    linPrefixCost, Prim.boundSize, linPermPowCost, linPermPowUnit,
    linAssignCost, linAssignRepCost, linAssignZeroWt, linAssignInitWt,
    linAssignUnitsArg, linAssignUnitCost, linAssignUnitStepCost, linAssignUnitAccWt,
    linAssignUnitBasisCost, linAssignUnitBasisArg, linBasisCost, linVectorAccWt,
    linIntCodecCost]
  gcongr

theorem linCoordinatePrepBudget_poly (ho : GroupOrder) :
    PBU (fun _ W _ => linCoordinatePrepBudget ho W) := by
  simp only [linCoordinatePrepBudget, linCoordinatePrepCost, linPrefixOrderCost,
    linPrefixOrderRatioCost, linPrefixCost, Prim.boundSize, linPermPowCost, linPermPowUnit,
    linAssignCost, linAssignRepCost, linAssignZeroWt, linAssignInitWt,
    linAssignUnitsArg, linAssignUnitCost, linAssignUnitStepCost, linAssignUnitAccWt,
    linAssignUnitBasisCost, linAssignUnitBasisArg, linBasisCost, linVectorAccWt,
    linIntCodecCost]
  norm_poly

theorem linCoordinateBudget_poly (ho : GroupOrder) (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linCoordinateBudget ho hm W) := by
  have hc := linCoordinatePrepBudget_poly ho
  have hj : PBU (fun _ W _ => linCoordinateMemberBudget W) := by
    unfold linCoordinateMemberBudget; norm_poly
  have hmout : PBU (fun _ W _ => linCoordinateMemberOutBudget hm W) := by
    unfold linCoordinateMemberOutBudget linCoordinateMemberBudget; norm_poly
  have hslp := linPoly_subst linSlpValueCost_poly PBU.W
    (PBU.smul 10 (PBU.addc (PBU.add hc hmout) 1)) (PBU.pow hj (linMembershipDegree hm))
  have hmem : PBU (fun _ W _ => (linMembershipPrim hm).boundSize (linCoordinateMemberBudget W)) := by
    unfold Prim.boundSize linCoordinateMemberBudget; norm_poly
  have hwit : PBU (fun _ W _ => linCoordinateWitnessBudget ho hm W) :=
    PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add hc PBU.W)
      (PBU.addc (PBU.add (PBU.add hmem hj) hmout) 2)) hmout) hslp) 1)
  have hrow : PBU (fun _ W _ => linCoordinateRowBudget ho hm W) :=
    PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.smul 10 (PBU.addc PBU.W 1)) hc) hwit) 1)
  unfold linCoordinateBudget linCoordinateCollectCost linVectorAccWt
  exact PBU.add (PBU.mul PBU.W (PBU.smul 10 (PBU.addc hrow 1)))
    (PBU.mul (PBU.smul loopModK (PBU.addc PBU.W 1))
      (PBU.addc (PBU.add (PBU.add PBU.W PBU.W)
        (PBU.addc (PBU.add (PBU.smul 2 (PBU.mul PBU.W hrow)) PBU.W) 4)) 1))

/-- The dense permutation encoding bounds the degree and both generator counts. -/
theorem linCoordinateSource_bounds {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) :
    let W := (Val.list [encGroup ns, encGroup as]).wt
    n ≤ W ∧ ns.length ≤ W ∧ as.length ≤ W := by
  have wn := S_le_wt_encGroup ns
  have wa := S_le_wt_encGroup as
  have wns : (encGroup ns).wt < (Val.list [encGroup ns, encGroup as]).wt := wt_le_wt_list (by simp)
  have was : (encGroup as).wt < (Val.list [encGroup ns, encGroup as]).wt := wt_le_wt_list (by simp)
  dsimp only
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- Powering changes the permutation entries but does not increase their encoded size. -/
theorem linCoordinateMember_wt {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : Fin as.length) :
    (memberInput (linCoordinateMemberInst ns as i)).wt ≤
      linCoordinateMemberBudget (Val.list [encGroup ns, encGroup as]).wt := by
  let W := (Val.list [encGroup ns, encGroup as]).wt
  obtain ⟨hn, hns, has⟩ := linCoordinateSource_bounds ns as
  change n ≤ W at hn
  change ns.length ≤ W at hns
  change as.length ≤ W at has
  let gs := ns ++ as.take i.val
  have hl : gs.length ≤ 2 * W := by simp only [gs, List.length_append, List.length_take]; omega
  have wp (p : Equiv.Perm (Fin n)) : (encPerm p).wt ≤ 4 * (W + 1) ^ 2 :=
    (wt_encPerm_le p).trans (Nat.mul_le_mul_left 4
      (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2))
  have wg := linWtList (vs := (1 :: gs).map encPerm) (B := 4 * (W + 1) ^ 2) (by
    intro v hv; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv; exact wp p)
  have wg' := wt_list2_le (.nat n) (.list ((1 :: gs).map encPerm))
  have wm := wt_list2_le (encGroup gs) (encPerm (linCoordinateMemberInst ns as i).x)
  have wn := wt_nat_le n
  have wx := wp (linCoordinateMemberInst ns as i).x
  change (Val.list [encGroup gs, encPerm (linCoordinateMemberInst ns as i).x]).wt ≤ _
  change (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt ≤ _ at wg'
  simp only [List.length_map, List.length_cons] at wg
  have wh := Nat.mul_le_mul_right (4 * (W + 1) ^ 2) (by omega : gs.length + 1 ≤ 2 * W + 1)
  unfold linCoordinateMemberBudget
  change _ ≤ 100 * (W + 1) ^ 3
  dsimp only [encGroup, encPerms] at wm ⊢
  dsimp only [linCoordinateMemberInst] at wx wm ⊢
  have wgi : (Val.list ((1 :: gs).map encPerm)).wt ≤
      2 * ((2 * W + 1) * (4 * (W + 1) ^ 2)) + (2 * W + 1) + 4 := by omega
  have wmi : (Val.list [.list [.nat n, .list ((1 :: gs).map encPerm)],
      encPerm (linCoordinateMemberInst ns as i).x]).wt ≤
      4 * (W + 2) + 4 * (2 * ((2 * W + 1) * (4 * (W + 1) ^ 2)) + (2 * W + 1) + 4) +
        8 * (W + 1) ^ 2 + 18 := by
    dsimp only [linCoordinateMemberInst]
    omega
  dsimp only [linCoordinateMemberInst] at wmi
  nlinarith only [wmi]

end GI.Impl
