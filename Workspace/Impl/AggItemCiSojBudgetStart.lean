import Workspace.Impl.AggItemCiSojFrameWt

/-! # Fixed-stage bounds for constructing the first rectangle -/

namespace GI.Impl

open GI.Lang

/-- Enlarge a fixed stage index before applying another program bound. -/
theorem itcs_budget_lift (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W : ℕ) {i j a : ℕ} (hij : i ≤ j)
    (ha : a ≤ (itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) :
    a ≤ (itcsGrow pf Bc Br hBc hBr)^[j] (W+100) :=
  ha.trans (Function.monotone_iterate_of_id_le (itcs_grow_le pf Bc Br hBc hBr) hij (W+100))

/-- One growth step pays any of the linear structural bookkeeping costs. -/
theorem itcs_budget_linear (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W i : ℕ) {a : ℕ}
    (ha : a ≤ 10^9*((itcsGrow pf Bc Br hBc hBr)^[i] (W+100)+100)) :
    a ≤ (itcsGrow pf Bc Br hBc hBr)^[i+1] (W+100) := by
  exact (ha.trans (itcs_wrapper_linear _)).trans
    (itcs_budget_local pf Bc Br hBc hBr (f:=itcsWrapperC) (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[18]? = some itcsWrapperC from rfl))
      W i (le_refl _))

/-- Every fixed growth stage covers the padded parent input. -/
theorem itcs_budget_base (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W i : ℕ) :
    W+100 ≤ (itcsGrow pf Bc Br hBc hBr)^[i] (W+100) :=
  itcs_budget_lift pf Bc Br hBc hBr W (i:=0) (Nat.zero_le i) (le_refl _)

/-- The actual physical-data and color-state wrappers use two successive
linear encoding stages. -/
theorem itcs_budget_twolinear (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W i : ℕ) :
    10^9*(10^9*((itcsGrow pf Bc Br hBc hBr)^[i] (W+100)+100)+100) ≤
      (itcsGrow pf Bc Br hBc hBr)^[i+2] (W+100) := by
  have h := itcs_budget_linear pf Bc Br hBc hBr W i (le_refl _)
  exact itcs_budget_linear pf Bc Br hBc hBr W (i+1)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 100))

/-- A request's paid-for output and answer weight imply the retained-frame cap
required by the common item relation. -/
theorem itcs_budget_frame {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k}
    {S : GI.Algorithm.State Ω C} {L : GI.Algorithm.GiantLabels S}
    (F : itcsQFrame e S L) (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (W : ℕ)
    {i : ℕ} (hi : i+1 ≤ 126)
    (hr : (itcsAskV (F.query 1) F.payload (.list F.pending)).wt ≤
      (itcsGrow pf Bc Br hBc hBr)^[i] (W+100))
    (ha : ansW k ≤ (itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) :
    F.weight ≤ (itcsGrow pf Bc Br hBc hBr)^[126] (W+100) :=
  itcs_budget_lift pf Bc Br hBc hBr W hi
    (itcs_budget_linear pf Bc Br hBc hBr W i (F.weight_request_bound hr ha))

end GI.Impl
