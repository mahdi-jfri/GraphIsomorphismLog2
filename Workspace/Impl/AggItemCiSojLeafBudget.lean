import Workspace.Impl.AggItemCiSojParentBudget

/-! # All first-rectangle leaf calls fit the first analysis stage -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang

/-- Own costs of the actual source, side, and physical-data leaf programs. -/
structure itcsLeafBounds (k q B A n : ℕ) : Prop where
  front : itcsFrontC q B ≤ n
  balance : itcsBalTC q B ≤ n
  test : itcsBTC q B ≤ n
  balpart : itcsBalPartC q B ≤ n
  imppart : itcsImpPartC q B ≤ n
  side : itcsSideC q B ≤ n
  guard : itcsGuardC q ≤ n
  fix : itcsFixProgC q ≤ n
  mark : itcsMarkC q ≤ n
  phys : itcsPhysC (k+q+k^2+2) ≤ n
  lc : itcsSwapLcC (k+q+k^2+2) ≤ n
  dom : itcsDomC k q ≤ n
  pull : itcsPullC k q B ≤ n
  align : itcsAlignC A ≤ n
  range : 7000*(q+1)^3 ≤ n
  compose : permK*(q+1)^3 ≤ n

/-- Parent-size substitution for every leaf bound uses monotonicity of its
proved formula. The cited certificate and representation costs are handled at
their actual encoded input sizes in later stages. -/
theorem itcs_leaf_bounds (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W k q B : ℕ) (hk : k≤ W) (hq : q≤2*W+3) (hB : B≤2*(2*W+3)^64) :
    itcsLeafBounds k q B (100*(2*W+4)^2) (itcsGrow pf Bc Br hBc hBr (W+100)) := by
  have profile {f : ℕ → ℕ} (hf : f∈itcsCostFns pf Bc Br) :
      f W ≤ itcsGrow pf Bc Br hBc hBr (W+100) :=
    itcs_parent_profile pf Bc Br hBc hBr W hf
  have hp : k+q+k^2+2 ≤ W+(2*W+3)+W^2+2 :=
    Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hk hq) (Nat.pow_le_pow_left hk 2)) 2
  have rangeBound : 7000*(q+1)^3 ≤ 56000*(W+2)^3 := by
    have h := Nat.mul_le_mul_left 7000 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3)
    have he : 7000*(2*W+3+1)^3=56000*(W+2)^3 := by ring
    exact h.trans_eq he
  have cmpBound : permK*(q+1)^3 ≤ 240000*(W+2)^3 := by
    have h := Nat.mul_le_mul_left permK (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3)
    have he : permK*(2*W+3+1)^3=240000*(W+2)^3 := by simp only [permK]; ring
    exact h.trans_eq he
  have balpart := (itcs_bal_part_cost_mono hq hB).trans
    (profile (f:=fun W => itcsBalPartC (2*W+3) (2*(2*W+3)^64)) (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[4]?=
      some (fun W => itcsBalPartC (2*W+3) (2*(2*W+3)^64)) from rfl)))
  refine ⟨?_,?_,?_,balpart,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (itcs_front_cost_mono hq hB).trans (profile (f:=fun W => itcsFrontC (2*W+3) (2*(2*W+3)^64))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[2]?=
        some (fun W => itcsFrontC (2*W+3) (2*(2*W+3)^64)) from rfl)))
  · exact (show itcsBalTC q B ≤ itcsBalPartC q B by unfold itcsBalPartC; omega).trans balpart
  · exact (itcs_bal_test_cost_mono hq hB).trans (profile (f:=fun W => itcsBTC (2*W+3) (2*(2*W+3)^64))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[3]?=
        some (fun W => itcsBTC (2*W+3) (2*(2*W+3)^64)) from rfl)))
  · exact (itcs_imp_part_cost_mono hq hB).trans (profile (f:=fun W => itcsImpPartC (2*W+3) (2*(2*W+3)^64))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[5]?=
        some (fun W => itcsImpPartC (2*W+3) (2*(2*W+3)^64)) from rfl)))
  · exact (itcs_side_cost_mono hq hB).trans (profile (f:=fun W => itcsSideC (2*W+3) (2*(2*W+3)^64))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[6]?=
        some (fun W => itcsSideC (2*W+3) (2*(2*W+3)^64)) from rfl)))
  · exact (itcs_guard_cost_mono hq).trans (profile (f:=fun W => itcsGuardC (2*W+3))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[7]?=some (fun W => itcsGuardC (2*W+3)) from rfl)))
  · exact (itcs_fix_prog_cost_mono hq).trans (profile (f:=fun W => itcsFixProgC (2*W+3))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[8]?=some (fun W => itcsFixProgC (2*W+3)) from rfl)))
  · exact (itcs_mark_cost_mono hq).trans (profile (f:=fun W => itcsMarkC (2*W+3))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[9]?=some (fun W => itcsMarkC (2*W+3)) from rfl)))
  · exact (itcs_phys_cost_mono hp).trans (profile (f:=fun W => itcsPhysC (W+(2*W+3)+W^2+2))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[10]?=some (fun W => itcsPhysC (W+(2*W+3)+W^2+2)) from rfl)))
  · exact (itcs_swap_lc_cost_mono hp).trans (profile (f:=fun W => itcsSwapLcC (W+(2*W+3)+W^2+2))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[11]?=some (fun W => itcsSwapLcC (W+(2*W+3)+W^2+2)) from rfl)))
  · exact (itcs_dom_cost_mono hk hq).trans (profile (f:=fun W => itcsDomC W (2*W+3))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[12]?=some (fun W => itcsDomC W (2*W+3)) from rfl)))
  · exact (itcs_pull_cost_mono hk hq hB).trans (profile (f:=fun W => itcsPullC W (2*W+3) (2*(2*W+3)^64))
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[13]?=some (fun W => itcsPullC W (2*W+3) (2*(2*W+3)^64)) from rfl)))
  · exact profile (f:=fun W => itcsAlignC (100*(2*W+4)^2)) (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[17]?=some (fun W => itcsAlignC (100*(2*W+4)^2)) from rfl))
  · exact rangeBound.trans (itcs_parent_small_stage pf Bc Br hBc hBr W 56000 2 3 (by decide) (by decide) (by decide))
  · exact cmpBound.trans (itcs_parent_small_stage pf Bc Br hBc hBr W 240000 2 3 (by decide) (by decide) (by decide))

end GI.Impl
