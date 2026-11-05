module

public import Workspace.Impl.AggItemCiSojBudget
public import Mathlib.Order.Iterate

@[expose] public section

/-! # Comparing the fixed encoding stages with the common item budget -/

namespace GI.Impl

open GI.Lang

/-- The common budget grows at every step. -/
theorem itcs_grow_le (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W : ℕ) :
    W ≤ itcsGrow pf Bc Br hBc hBr W :=
  (Nat.le_add_right W 1).trans (itcs_envelope_grow _ _ W)

/-- Every one of the fixed encoding stages fits the final budget. -/
theorem itcs_budget_iter_le (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W : ℕ) {i : ℕ} (hi : i ≤ 128) :
    (itcsGrow pf Bc Br hBc hBr)^[i] (W+100) ≤ itcsXs pf Bc Br hBc hBr W := by
  have hg : (id : ℕ → ℕ) ≤ itcsGrow pf Bc Br hBc hBr := itcs_grow_le pf Bc Br hBc hBr
  have h := Function.monotone_iterate_of_id_le hg hi (W+100)
  exact h.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 1000))

/-- The final budget bounds the input and the constant init cost. -/
theorem itcs_budget_input (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W : ℕ) :
    W+100 ≤ itcsXs pf Bc Br hBc hBr W :=
  itcs_budget_iter_le pf Bc Br hBc hBr W (i:=0) (by decide)

/-- Any established callee bound at an input covered by an earlier stage fits
the final item budget. -/
theorem itcs_budget_stage (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {f : ℕ → ℕ} (hf : f ∈ itcsCostFns pf Bc Br) (W : ℕ) {i a : ℕ}
    (hi : i < 128) (ha : a ≤ (itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) :
    f a ≤ itcsXs pf Bc Br hBc hBr W := by
  have hs := itcs_stage_cost_le pf Bc Br hBc hBr hf ha
  have he : itcsGrow pf Bc Br hBc hBr ((itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) =
      (itcsGrow pf Bc Br hBc hBr)^[i+1] (W+100) := (Function.iterate_succ_apply' ..).symm
  rw [he] at hs
  exact hs.trans (itcs_budget_iter_le pf Bc Br hBc hBr W (by omega))

/-- The analysis growth function is monotone. -/
theorem itcs_grow_mono (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    Monotone (itcsGrow pf Bc Br hBc hBr) := itcs_envelope_mono _ _

/-- Two remaining fixed encoding stages. -/
theorem itcs_iter_twice (g : ℕ → ℕ) (i W : ℕ) :
    g^[i+2] W = g (g (g^[i] W)) := by
  rw [Function.iterate_succ_apply',Function.iterate_succ_apply']

/-- A frame built by stage 126 leaves two growth steps for the actual queue
and finalizer wrapper before the global budget is reached. -/
theorem itcs_budget_tail (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W : ℕ) {a : ℕ}
    (ha : a ≤ (itcsGrow pf Bc Br hBc hBr)^[126] (W+100)) :
    itcsGrow pf Bc Br hBc hBr (itcsGrow pf Bc Br hBc hBr a) ≤ itcsXs pf Bc Br hBc hBr W := by
  have h := itcs_grow_mono pf Bc Br hBc hBr (itcs_grow_mono pf Bc Br hBc hBr ha)
  have he := (itcs_iter_twice (itcsGrow pf Bc Br hBc hBr) 126 (W+100)).symm
  rw [he] at h
  exact h.trans (itcs_budget_iter_le pf Bc Br hBc hBr W (i:=128) (by decide))

/-- A listed stage cost at an earlier covered input fits the immediately next
analysis stage, before passing to the final item budget. -/
theorem itcs_budget_local (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {f : ℕ → ℕ} (hf : f ∈ itcsCostFns pf Bc Br) (W i : ℕ) {a : ℕ}
    (ha : a ≤ (itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) :
    f a ≤ (itcsGrow pf Bc Br hBc hBr)^[i+1] (W+100) := by
  simpa only [Function.iterate_succ_apply'] using itcs_stage_cost_le pf Bc Br hBc hBr hf ha

end GI.Impl
