module

public import Workspace.Impl.SNFTabs
public import Workspace.Impl.HNFPoly
public import Workspace.Impl.LinDenseMul

@[expose] public section

/-!
# One polynomial envelope for the costs used by the Smith program

`SnfEnv K D` says that every library cost the Smith program uses is at most `K (w + 2)^D` on
inputs of weight `w`: the Hermite program, the dense product, the two tables, the numbers `K, m`
of the Hermite program, and the integer operations. `snfEnv_exists` gives such `K, D`, from the
polynomial bounds `hnfMainCost_poly`, `linDenseMulCost_poly`, and `hnf_norm_poly` for the rest.
-/

namespace GI.Impl

open GI.Cited GI.Lang

/-- The envelope of the library costs. -/
structure SnfEnv (K D : ℕ) : Prop where
  one_le : 1 ≤ K
  d_pos : 1 ≤ D
  hnf : ∀ w, hnfMainCost w ≤ K * (w + 2) ^ D
  mul : ∀ m w, m ≤ w → linMatrixMulCost w m m m ≤ K * (w + 2) ^ D
  tr : ∀ X, hnfTabCost X (hnfHCellCost (10 * X + 18)) ≤ K * (X + 2) ^ D
  emb : ∀ X, hnfTabCost X (snfEmbCellCost (10 * X + 18)) ≤ K * (X + 2) ^ D
  nums : ∀ Y, hnfNumsCost Y ≤ K * (Y + 2) ^ D
  ints : ∀ w, linIntBinaryCost w ≤ K * (w + 2) ^ D

theorem snfEnv_mono {K D : ℕ} (w w' : ℕ) (h : w ≤ w') : K * (w + 2) ^ D ≤ K * (w' + 2) ^ D :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem snfTrCost_poly : PBU (fun _ X _ => hnfTabCost X (hnfHCellCost (10 * X + 18))) := by
  simp only [hnfTabCost, hnfTabRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget,
    hnfHCellCost]
  hnf_norm_poly

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem snfEmbCost_poly : PBU (fun _ X _ => hnfTabCost X (snfEmbCellCost (10 * X + 18))) := by
  simp only [hnfTabCost, hnfTabRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget,
    snfEmbCellCost]
  hnf_norm_poly

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem snfNumsCost_poly : PBU (fun _ Y _ => hnfNumsCost Y) := by
  simp only [linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost, hnfNumsCost,
    hnfMatAbsCost, hnfRowAbsCost, hnfAbsStepCost, hnfPowCost, linTabulateCost,
    linTabulateRangeCost, linMapBudget]
  hnf_norm_poly

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem snfIntsCost_poly : PBU (fun _ w _ => linIntBinaryCost w) := by
  simp only [linIntBinaryCost, linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  hnf_norm_poly

/-- A uniform bound from `PBU` for a function of `w` alone. -/
theorem snf_of_pbu {f : ℕ → ℕ} (h : PBU fun _ w _ => f w) : ∃ C D, ∀ w, f w ≤ C * (w + 2) ^ D := by
  obtain ⟨C, D, h⟩ := h
  exact ⟨C, D, fun w => by simpa [PB] using h 0 w 0⟩

/-- Raise a bound `C (w + 2)^D` to `K (w + 2)^E` with `C ≤ K`, `D ≤ E`. -/
theorem snf_raise {a C D K E w : ℕ} (h : a ≤ C * (w + 2) ^ D) (hC : C ≤ K) (hD : D ≤ E) :
    a ≤ K * (w + 2) ^ E :=
  h.trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hD))

theorem snfEnv_exists : ∃ K D, SnfEnv K D := by
  obtain ⟨C1, D1, h1⟩ := snf_of_pbu hnfMainCost_poly
  obtain ⟨C2, D2, h2⟩ := linDenseMulCost_poly
  obtain ⟨C3, D3, h3⟩ := snf_of_pbu snfTrCost_poly
  obtain ⟨C4, D4, h4⟩ := snf_of_pbu snfEmbCost_poly
  obtain ⟨C5, D5, h5⟩ := snf_of_pbu snfNumsCost_poly
  obtain ⟨C6, D6, h6⟩ := snf_of_pbu snfIntsCost_poly
  set D := D1 + D2 + D3 + D4 + D5 + D6 + 1
  set K := C1 + C2 * 2 ^ D2 + C3 + C4 + C5 + C6 + 1
  refine ⟨K, D, ⟨by omega, by omega, fun w => snf_raise (h1 w) (by omega) (by omega), fun m w hm => ?_,
    fun X => snf_raise (h3 X) (by omega) (by omega), fun X => snf_raise (h4 X) (by omega) (by omega),
    fun Y => snf_raise (h5 Y) (by omega) (by omega), fun w => snf_raise (h6 w) (by omega) (by omega)⟩⟩
  have h := h2 m w 0
  unfold PB at h
  have e1 : (w + 0 + m + 2) ^ D2 ≤ (2 * (w + 2)) ^ D2 := Nat.pow_le_pow_left (by omega) D2
  have e2 : (2 * (w + 2)) ^ D2 = 2 ^ D2 * (w + 2) ^ D2 := mul_pow _ _ _
  have h' : linMatrixMulCost w m m m ≤ C2 * 2 ^ D2 * (w + 2) ^ D2 := by
    calc _ ≤ C2 * (w + 0 + m + 2) ^ D2 := h
      _ ≤ C2 * (2 ^ D2 * (w + 2) ^ D2) := Nat.mul_le_mul_left _ (e2 ▸ e1)
      _ = _ := by ring
  exact snf_raise h' (by omega) (by omega)

end GI.Impl
