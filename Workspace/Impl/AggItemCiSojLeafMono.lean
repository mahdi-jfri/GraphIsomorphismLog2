module

public import Workspace.Impl.AggItemCiSojBudget

@[expose] public section

/-! # Monotonicity of the actual fixed-stage own-cost formulas -/

namespace GI.Impl
open GI.Lang

/-- Increasing the size parameters increases the proved front bound. -/
theorem itcs_front_cost_mono {q B q' B' : ℕ} (hq : q ≤ q') (hB : B ≤ B') :
    itcsFrontC q B ≤ itcsFrontC q' B' := by
  have hcw : itcsCompW q B ≤ itcsCompW q' B' := by
    simp only [itcsCompW, itCfObjB, itcsGenW]; gcongr
  have hct : itcsCompTotal q B ≤ itcsCompTotal q' B' := by
    simp only [itcsCompTotal, itcsCompC, itcsSqMapC, itcsGenW]; gcongr
  have hsz : itcsSizeC q B ≤ itcsSizeC q' B' :=
    Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 30 (Nat.add_le_add_right hcw 1)) hct)
      (Nat.mul_le_mul_left (countK + 1000) (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3))
  simp only [itcsFrontC, itcsFindC, itcsFiberC, itcsTestC, itcsBalW, itCfObjB]
  gcongr

/-- Increasing the size parameters increases the proved bal test bound. -/
theorem itcs_bal_test_cost_mono {q B q' B' : ℕ} (hq : q ≤ q') (hB : B ≤ B') :
    itcsBTC q B ≤ itcsBTC q' B' := by
  simp only [itcsBTC, itcsBTW, countK, loopModK]
  gcongr

/-- Increasing the size parameters increases the proved bal part bound. -/
theorem itcs_bal_part_cost_mono {q B q' B' : ℕ} (hq : q ≤ q') (hB : B ≤ B') :
    itcsBalPartC q B ≤ itcsBalPartC q' B' := by
  simp only [itcsBalPartC, itcsBalPartW, itcsBalM, itcsBalTC, itcsBalW, itCfObjB, itciFC, mapK]
  gcongr

/-- Increasing the size parameters increases the proved imp part bound. -/
theorem itcs_imp_part_cost_mono {q B q' B' : ℕ} (hq : q ≤ q') (hB : B ≤ B') :
    itcsImpPartC q B ≤ itcsImpPartC q' B' := by
  have hcw : itcsCompW q B ≤ itcsCompW q' B' := by
    simp only [itcsCompW, itCfObjB, itcsGenW]; gcongr
  have hct : itcsCompTotal q B ≤ itcsCompTotal q' B' := by
    simp only [itcsCompTotal, itcsCompC, itcsSqMapC, itcsGenW]; gcongr
  simp only [itcsImpPartC, itcsImpPartW, itcsMinC, itcsMinW, itC1C, itCfObjB]
  gcongr

/-- Increasing the size parameters increases the proved side bound. -/
theorem itcs_side_cost_mono {q B q' B' : ℕ} (hq : q ≤ q') (hB : B ≤ B') :
    itcsSideC q B ≤ itcsSideC q' B' := by
  simp only [itcsSideC, itcsSideW, itcsBalM, mapK]
  gcongr

/-- Increasing the size parameters increases the proved fix prog bound. -/
theorem itcs_fix_prog_cost_mono {q q' : ℕ} (hq : q ≤ q') :
    itcsFixProgC q ≤ itcsFixProgC q' := by
  simp only [itcsFixProgC,itcsFixProgW,itcsFixGenC,itciFC,itcsFixMarkC,itcsMarkW,mapK]
  gcongr

/-- Increasing the size parameters increases the proved mark bound. -/
theorem itcs_mark_cost_mono {q q' : ℕ} (hq : q ≤ q') :
    itcsMarkC q ≤ itcsMarkC q' := by
  simp only [itcsMarkC,itcsMarkW,mapK]
  gcongr

/-- Increasing the size parameters increases the proved guard bound. -/
theorem itcs_guard_cost_mono {q q' : ℕ} (hq : q ≤ q') :
    itcsGuardC q ≤ itcsGuardC q' := by
  simp only [itcsGuardC, itcsGuardW, countK]
  gcongr

/-- Increasing the size parameters increases the proved phys bound. -/
theorem itcs_phys_cost_mono {M M' : ℕ} (hM : M ≤ M') :
    itcsPhysC M ≤ itcsPhysC M' := by
  simp only [itcsPhysC,itcsPhysW,mkGroupK,mapK]
  gcongr

/-- Increasing the size parameters increases the proved swap lc bound. -/
theorem itcs_swap_lc_cost_mono {M M' : ℕ} (hM : M ≤ M') :
    itcsSwapLcC M ≤ itcsSwapLcC M' := by
  simp only [itcsSwapLcC, itcsSwapLcW, itHvLcC, swapMapK]
  gcongr

/-- Increasing the size parameters increases the proved dom bound. -/
theorem itcs_dom_cost_mono {k q k' q' : ℕ} (hk : k ≤ k') (hq : q ≤ q') :
    itcsDomC k q ≤ itcsDomC k' q' := by
  simp only [itcsDomC,itcsDomW,mapK]
  gcongr

/-- Increasing the size parameters increases the proved pull bound. -/
theorem itcs_pull_cost_mono {k q B k' q' B' : ℕ} (hk : k ≤ k') (hq : q ≤ q') (hB : B ≤ B') :
    itcsPullC k q B ≤ itcsPullC k' q' B' := by
  simp only [itcsPullC,itcsPullW,itCfObjB,mapK]
  gcongr

/-- The fixed alignment encoder has a monotone scalar own-cost bound. -/
theorem itcs_align_cost_mono {a b : ℕ} (h : a ≤ b) : itcsAlignC a ≤ itcsAlignC b := by
  simp only [itcsAlignC,itciFC]
  gcongr

end GI.Impl
