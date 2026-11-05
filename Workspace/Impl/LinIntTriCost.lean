module

public import Workspace.Impl.LinIntTrim

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- One global size parameter through the triangular recursion. It drops by one
when a row and column are removed, even though the residual bit bound increases. -/
def linTriSize (n B C : ℕ) : ℕ := n + B + C + n * (B + 1) + 1

/-- A polynomial bound on every mathematical matrix, vector or scalar value. -/
def linTriDataBudget (T : ℕ) : ℕ := 1000 * (T + 1) ^ 4

def linTriArgBudget (T : ℕ) : ℕ := 20 * linTriDataBudget T + 100

/-- A fixed polynomial bounds all nonrecursive work in a substitution call. -/
def linTriUnitCost (T : ℕ) : ℕ :=
  let A := linTriArgBudget T
  10000 * (linIntDivModCost A + linTailCost A + linTrimCost A T +
    linVectorScaleCost A T + linVectorBinaryCost A T (20 * (A + 2)) +
    loopModK * (T + 1) * (A + T + linTriDataBudget T + 1) + A + T + 1)

def linTriCost (n B C : ℕ) : ℕ := (n + 1) * linTriUnitCost (linTriSize n B C)

theorem linTriSize_step (n B C : ℕ) :
    linTriSize n B (C + B + 1) + 1 = linTriSize (n + 1) B C := by unfold linTriSize; ring

attribute [gcongr] linVectorScaleCost_mono linVectorBinaryCost_mono linTrimCost_mono

theorem linTriUnitCost_mono {S T : ℕ} (h : S ≤ T) : linTriUnitCost S ≤ linTriUnitCost T := by
  have hd : linTriDataBudget S ≤ linTriDataBudget T := by unfold linTriDataBudget; gcongr
  have ha : linTriArgBudget S ≤ linTriArgBudget T := by unfold linTriArgBudget; omega
  have he : linIntDivModCost (linTriArgBudget S) ≤ linIntDivModCost (linTriArgBudget T) := by
    unfold linIntDivModCost
    gcongr
  dsimp only [linTriUnitCost]
  gcongr

/-- Dense matrices with at most T rows and columns and T-bit entries fit the data budget. -/
theorem linTriMatrixBudget {n B T : ℕ} (hn : n ≤ T) (hB : B ≤ T)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : EntriesBits B H) :
    (encIntMatrix H).wt ≤ linTriDataBudget T := by
  have hw := linWtMatrix hH
  have hm : linMatrixWt n n B ≤ linMatrixWt T T T := by unfold linMatrixWt; gcongr
  have htop : linMatrixWt T T T ≤ linTriDataBudget T := by unfold linMatrixWt linTriDataBudget; ring_nf; omega
  exact hw.trans (hm.trans htop)

/-- The same budget bounds dense integer rows of polynomial-bit entries. -/
theorem linTriVectorBudget {n C T : ℕ} (hn : n ≤ T) (hC : C ≤ T) (w : Fin n → ℤ)
    (hw : ∀ i, (w i).natAbs < 2 ^ C) : (linVecVal w).wt ≤ linTriDataBudget T := by
  have hv := linWtList (vs := (List.finRange n).map fun i => encInt (w i)) (B := 20 * (C + 1)) (by
    intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv; exact linWtInt (hw i))
  have hl : (linVecVal w).wt ≤ linVectorAccWt n (20 * (C + 1)) := by simpa [linVecVal, linVectorAccWt] using hv
  have hm := linVectorAccWt_mono hn (show 20 * (C + 1) ≤ 20 * (T + 1) by omega)
  have htop : linVectorAccWt T (20 * (T + 1)) ≤ linTriDataBudget T := by
    unfold linVectorAccWt linTriDataBudget
    ring_nf
    omega
  exact hl.trans (hm.trans htop)

theorem linTriScalarBudget {C T : ℕ} (hC : C ≤ T) (x : ℤ) (hx : x.natAbs < 2 ^ C) :
    (encInt x).wt ≤ linTriDataBudget T := by
  have hw := linWtInt hx
  unfold linTriDataBudget
  ring_nf
  omega

theorem linIntDivModCost_mono {W V : ℕ} (h : W ≤ V) : linIntDivModCost W ≤ linIntDivModCost V := by
  have hc := linIntBinaryCost_mono h
  unfold linIntDivModCost
  omega

theorem linTriDataBudget_le_arg (T : ℕ) : linTriDataBudget T ≤ linTriArgBudget T := by
  unfold linTriArgBudget
  omega

theorem linTriSize_le_arg (T : ℕ) : T ≤ linTriArgBudget T := by
  unfold linTriArgBudget linTriDataBudget
  ring_nf
  omega

theorem linTriCost_mono {n m B D C E : ℕ} (hn : n ≤ m) (hB : B ≤ D) (hC : C ≤ E) :
    linTriCost n B C ≤ linTriCost m D E := by
  have hs : linTriSize n B C ≤ linTriSize m D E := by unfold linTriSize; gcongr
  unfold linTriCost
  exact Nat.mul_le_mul (by omega) (linTriUnitCost_mono hs)

end GI.Impl
