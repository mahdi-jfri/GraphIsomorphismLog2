module

public import Workspace.Impl.LinCoordinateCost

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem linCoordinateCollectCost_mono {W V t s D E : ℕ}
    (hW : W ≤ V) (ht : t ≤ s) (hD : D ≤ E) :
    linCoordinateCollectCost W t D ≤ linCoordinateCollectCost V s E := by
  simp only [linCoordinateCollectCost, linVectorAccWt]
  gcongr

theorem linCoordinateRowCost_le (ho : GroupOrder) (hm : ConstructiveMembership)
    {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : Fin as.length) :
    linCoordinateRowCost ho hm ns as i ≤
      linCoordinateRowBudget ho hm (Val.list [encGroup ns, encGroup as]).wt := by
  let W := (Val.list [encGroup ns, encGroup as]).wt
  let Wp := (Val.list [encGroup ns, encGroup as, .nat i.val]).wt
  let I := linCoordinateMemberInst ns as i
  let C := linCoordinatePrepCost ho Wp n ns.length as.length i.val
  let CB := linCoordinatePrepBudget ho W
  let J := linCoordinateMemberBudget W
  let MW := linCoordinateMemberOutBudget hm W
  obtain ⟨hn, hns, ht⟩ := linCoordinateSource_bounds ns as
  change n ≤ W at hn
  change ns.length ≤ W at hns
  change as.length ≤ W at ht
  have hi : i.val ≤ W := i.isLt.le.trans ht
  have wns : (encGroup ns).wt < W := wt_le_wt_list (by simp [W])
  have was : (encGroup as).wt < W := wt_le_wt_list (by simp [W])
  have wp : Wp ≤ 10 * (W + 1) := by
    have hh := wt_list3_le (encGroup ns) (encGroup as) (.nat i.val)
    have hh' := wt_nat_le i.val
    dsimp only [Wp]; omega
  have hC : C ≤ CB := linCoordinatePrepCost_mono ho wp hn hns ht hi
  have hmwt : (memberInput I).wt ≤ J := linCoordinateMember_wt ns as i
  have hs : (memberInput I).cells.length ≤ J := (memberInput I).size_le_wt.trans hmwt
  have hg : I.gs.length ≤ 2 * W := by
    simp only [I, linCoordinateMemberInst, List.length_append, List.length_take]
    omega
  have hout : linMembershipWt (linMembershipDegree hm) I ≤ MW := by
    change 400 * (((memberInput I).cells.length ^ linMembershipDegree hm) + 1) *
      (I.gs.length + (memberInput I).cells.length ^ linMembershipDegree hm + 2) + 100 ≤
      400 * (J ^ linMembershipDegree hm + 1) * (2 * W + J ^ linMembershipDegree hm + 2) + 100
    have hp := Nat.pow_le_pow_left hs (linMembershipDegree hm)
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 1)
    · omega
  have hcall : linMembershipCost hm I ≤ (linMembershipPrim hm).boundSize J + J + MW + 2 := by
    have hp := (linMembershipPrim hm).bound_le hs
    unfold linMembershipCost
    omega
  have he := linSlpValueCost_mono_all
    (by omega : 10 * (C + linMembershipWt (linMembershipDegree hm) I + 1) ≤ 10 * (CB + MW + 1))
    (Nat.pow_le_pow_left hs (linMembershipDegree hm)) ht
  have hwit : linCoordinateWitnessCost hm I C as.length ≤ linCoordinateWitnessBudget ho hm W := by
    change 1000 * (C + as.length + linMembershipCost hm I + linMembershipWt (linMembershipDegree hm) I +
      linSlpValueCost (10 * (C + linMembershipWt (linMembershipDegree hm) I + 1))
        ((memberInput I).cells.length ^ linMembershipDegree hm) as.length + 1) ≤
      1000 * (CB + W + ((linMembershipPrim hm).boundSize J + J + MW + 2) + MW +
        linSlpValueCost (10 * (CB + MW + 1)) (J ^ linMembershipDegree hm) W + 1)
    omega
  change 1000 * (Wp + C + linCoordinateWitnessCost hm I C as.length + 1) ≤ _
  unfold linCoordinateRowBudget
  change _ ≤ 1000 * (10 * (W + 1) + CB + linCoordinateWitnessBudget ho hm W + 1)
  omega

/-- The complete collection has uniform polynomial bit cost in the two source groups. -/
theorem linCoordinateCollectCost_poly (ho : GroupOrder) (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {n : ℕ} (ns as : List (Equiv.Perm (Fin n))),
      linCoordinateCollectCost (Val.list [encGroup ns, encGroup as]).wt as.length
        (linCoordinateRowBudget ho hm (Val.list [encGroup ns, encGroup as]).wt) ≤
      K * ((Val.list [encGroup ns, encGroup as]).wt + 1) ^ D := by
  obtain ⟨K, D, hp⟩ := linCoordinateBudget_poly ho hm
  refine ⟨K * 2 ^ D, D, fun ns as => ?_⟩
  let W := (Val.list [encGroup ns, encGroup as]).wt
  have ht := (linCoordinateSource_bounds ns as).2.2
  have hle : linCoordinateCollectCost W as.length (linCoordinateRowBudget ho hm W) ≤
      linCoordinateBudget ho hm W := by
    exact linCoordinateCollectCost_mono le_rfl ht le_rfl
  have hb := hp 0 W 0
  change linCoordinateBudget ho hm W ≤ K * (W + 0 + 0 + 2) ^ D at hb
  calc
    _ ≤ linCoordinateBudget ho hm W := hle
    _ ≤ K * (W + 2) ^ D := by simpa using hb
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
