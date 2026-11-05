module

public import Workspace.Impl.LinPrimaryStepInput

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryTransportCost_mono (h : VectorStabilizer) {W V j k : ℕ}
    (hw : W ≤ V) (hj : j ≤ k) : linPrimaryTransportCost h W j ≤ linPrimaryTransportCost h V k := by
  have hi : linPrimaryTransportInputBudget W j ≤ linPrimaryTransportInputBudget V k :=
    linPrimaryInputCost_mono hw hj
  have ha : linPrimaryTransportArg W j ≤ linPrimaryTransportArg V k :=
    Nat.mul_le_mul_left 100 (Nat.add_le_add_right (Nat.add_le_add hw hi) 1)
  have hb : linPrimaryTransportAffineBudget h W j ≤ linPrimaryTransportAffineBudget h V k :=
    linAffineTransportCost_mono h ha
  exact Nat.mul_le_mul_left 100000 (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hw hi) hb) 1)

theorem linPrimarySuccessCost_mono (h : ConstructiveMembership) {W V : ℕ} (hw : W ≤ V) :
    linPrimarySuccessCost h W ≤ linPrimarySuccessCost h V := by
  have harg := Nat.mul_le_mul_left 100 (Nat.add_le_add_right hw 1)
  have hi : linPrimarySuccessItemBudget h W ≤ linPrimarySuccessItemBudget h V := linActionItemCost_mono h harg
  have ha : linPrimarySuccessPointArg h W ≤ linPrimarySuccessPointArg h V :=
    Nat.mul_le_mul_left 100 (Nat.add_le_add_right (Nat.add_le_add hw hi) 1)
  have hp : linPrimarySuccessPointBudget h W ≤ linPrimarySuccessPointBudget h V :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) _)
  have hr : linPrimarySuccessRestrictBudget h W ≤ linPrimarySuccessRestrictBudget h V :=
    linAffineRestrictCost_mono h harg
  have hc : linPrimarySuccessComposeBudget W ≤ linPrimarySuccessComposeBudget V :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) _)
  exact Nat.mul_le_mul_left 100000 (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hw hi) hp) hr) hc) 1)

def linPrimaryStepZeroBudget (W : ℕ) : ℕ := 100000 * (W + 1) ^ 3

def linPrimaryStepArgBudget (W : ℕ) : ℕ := 1000000 * (W + linPrimaryStepZeroBudget W + 1)
noncomputable def linPrimaryStepLayerBudget (h : VectorStabilizer) (W level : ℕ) : ℕ :=
  linPrimaryTransportCost h (linPrimaryStepArgBudget W) level
noncomputable def linPrimaryStepTailArg (h : VectorStabilizer) (W level : ℕ) : ℕ :=
  100 * (W + linPrimaryStepZeroBudget W + linPrimaryStepLayerBudget h W level + 1)
noncomputable def linPrimaryStepTailBudget (hm : ConstructiveMembership) (hv : VectorStabilizer)
    (W level : ℕ) : ℕ := linPrimarySuccessCost hm (linPrimaryStepTailArg hv W level)
noncomputable def linPrimaryStepCost (hm : ConstructiveMembership) (hv : VectorStabilizer)
    (W level : ℕ) : ℕ := 100000 * (W + linPrimaryStepZeroBudget W + linPrimaryStepArgBudget W +
      linPrimaryStepLayerBudget hv W level + linPrimaryStepTailBudget hm hv W level + 1)

theorem linPrimaryStepCost_poly (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    PBU (fun level W _ => linPrimaryStepCost hm hv W level) := by
  have hz : PBU (fun _ W _ => linPrimaryStepZeroBudget W) := by unfold linPrimaryStepZeroBudget; norm_poly
  have ha : PBU (fun _ W _ => linPrimaryStepArgBudget W) := PBU.smul 1000000 (PBU.addc (PBU.add PBU.W hz) 1)
  have hl : PBU (fun level W _ => linPrimaryStepLayerBudget hv W level) :=
    linPoly_subst (linPrimaryTransportCost_poly hv) PBU.k ha (PBU.const 0)
  have hta : PBU (fun level W _ => linPrimaryStepTailArg hv W level) :=
    PBU.smul 100 (PBU.addc (PBU.add (PBU.add PBU.W hz) hl) 1)
  have ht : PBU (fun level W _ => linPrimaryStepTailBudget hm hv W level) :=
    linPoly_subst (linPrimarySuccessCost_poly hm) (PBU.const 0) hta (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hz) ha) hl) ht) 1)

theorem linPrimaryStepCost_bit_bound (hm : ConstructiveMembership) (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ W level, level ≤ W → linPrimaryStepCost hm hv W level ≤ K * (W + 1) ^ D := by
  obtain ⟨K, D, h⟩ := linPoly_source_bound (linPrimaryStepCost_poly hm hv)
  exact ⟨K, D, fun W level hl => h level W W hl le_rfl⟩

end GI.Impl
