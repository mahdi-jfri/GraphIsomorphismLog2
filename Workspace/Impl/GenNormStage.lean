import Workspace.Impl.GenNormArgs

/-! # The uniform bound covers each preparation call -/
namespace GI.Impl
open GI.Lang
open GI.Cited (Preimage PointwiseStab Membership)

private theorem normAltCost_mono {m M : ℕ} (h : m ≤ M) : normAltCost m ≤ normAltCost M := by
  unfold normAltCost cycGensCost
  gcongr

variable (hp : Preimage) (hst : PointwiseStab) (hm : Membership)

theorem normBudget_cls {n T : ℕ} (hn : n ≤ T) :
    clsK * (n + 1) ^ 4 ≤ normStageBudget hp hst hm T := by
  have hx : clsK * (n + 1) ^ 4 ≤ clsK * (T + 1) ^ 4 := by gcongr
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_range {n T : ℕ} (hn : n ≤ T) :
    8000 * (n + 1) ^ 3 ≤ normStageBudget hp hst hm T := by
  have hx : 8000 * (n + 1) ^ 3 ≤ 8000 * (T + 1) ^ 3 := by gcongr
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_parent {n m L W T : ℕ} (hn : n ≤ T) (hm' : m ≤ T) (hL : L ≤ T) (hW : W ≤ normArgBudget T) :
    normParentListCost n m L W ≤ normStageBudget hp hst hm T := by
  have hx := normParentListCost_mono hn hm' hL hW
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_alt {m T : ℕ} (hm' : m ≤ T) :
    normAltCost m ≤ normStageBudget hp hst hm T := by
  have hx := normAltCost_mono hm'
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_graph {n m L T : ℕ} (hn : n ≤ T) (hm' : m ≤ T) (hL : L ≤ T) :
    normGraphCost hp n m L ≤ normStageBudget hp hst hm T := by
  have hx := normGraphCost_mono hp hn hm' hL
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_raw {n m L W T : ℕ} (hn : n ≤ T) (hm' : m ≤ T) (hL : L ≤ T) (hW : W ≤ normArgBudget T) :
    normRawReduceCost hst n m L W ≤ normStageBudget hp hst hm T := by
  have hx := normRawReduceCost_mono hst hn hm' hL hW
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_cosets {n L W T : ℕ} (hn : n ≤ T) (hL : L ≤ T) (hW : W ≤ normArgBudget T) :
    normCosetsCost hm n L W ≤ normStageBudget hp hst hm T := by
  have hx := normCosetsCost_mono hm hn hL hW
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_selection {W T : ℕ} (hW : W ≤ normArgBudget T) :
    hsplitK * (W + 1) ^ 5 ≤ normStageBudget hp hst hm T := by
  have hx : hsplitK * (W + 1) ^ 5 ≤ hsplitK * (normArgBudget T + 1) ^ 5 := by gcongr
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_count {n T : ℕ} (hn : n ≤ T) :
    countK * (n + 1) ^ 3 ≤ normStageBudget hp hst hm T := by
  have hx : countK * (n + 1) ^ 3 ≤ countK * (T + 1) ^ 3 := by gcongr
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_blocks {n m W T : ℕ} (hn : n ≤ T) (hm' : m ≤ T) (hW : W ≤ normArgBudget T) :
    normBlockMapCost n m W ≤ normStageBudget hp hst hm T := by
  have hx := normBlockMapCost_mono hn hm' hW
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_labels {m k W T : ℕ} (hm' : m ≤ T) (hk : k ≤ T) (hW : W ≤ normArgBudget T) :
    10 ^ 6 * (W + m + k + 1) ^ 2 ≤ normStageBudget hp hst hm T := by
  have hx : 10 ^ 6 * (W + m + k + 1) ^ 2 ≤ 10 ^ 6 * (normArgBudget T + T + T + 1) ^ 2 := by gcongr
  unfold normStageBudget
  dsimp only
  omega

theorem normBudget_orbit {n W T : ℕ} (hn : n ≤ T) (hW : W ≤ normArgBudget T) :
    normOrbitCost n W ≤ normStageBudget hp hst hm T := by
  have hx := normOrbitCost_mono hn hW
  unfold normStageBudget
  dsimp only
  omega

end GI.Impl
