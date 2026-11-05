module

public import Workspace.Impl.LinAffineHomogenize
public import Workspace.Lang.Prims.Other
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! The vector-stabilizer call used by each homogeneous affine layer.
The solvable cover and its explicit representation remain part of the input task. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linVectorStabilizerF (j : ℕ) : Expr := primF j

noncomputable def linVectorStabilizerCost (h : VectorStabilizer) (I : VecStabInst) : ℕ :=
  (vectorStabilizerPrim h).bound (vecStabEnc I) + (vecStabEnc I).wt + 13 * (I.n + 1) ^ 6 + 2

/-- One cited call, with the cost of writing the returned permutation generators. -/
theorem linVectorStabilizer_spec (h : VectorStabilizer) {P : Program} {f j : ℕ}
    (hf : P.funs[f]? = some (linVectorStabilizerF j))
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) (I : VecStabInst) :
    FunAll P f (vecStabEnc I) (fun out cost => GensVal I.n out (vecStabSub I) ∧
      cost ≤ linVectorStabilizerCost h I) := by
  refine (FunAll.prim_spec hf hj (vectorStabilizerPrim_spec h I)).mono fun out cost ho => ?_
  exact ⟨ho.1, by have hw := GensVal.wt_le ho.1; unfold linVectorStabilizerCost; omega⟩

/-- The cited vector call fits a uniform polynomial in the input weight.
The prime bound p ≤ n is already a field of VecStabInst. -/
theorem linVectorStabilizerCost_poly (h : VectorStabilizer) :
    ∃ K D : ℕ, ∀ I : VecStabInst,
      linVectorStabilizerCost h I ≤ K * ((vecStabEnc I).wt + 1) ^ D := by
  have hp : PBU (fun _ W _ => (vectorStabilizerPrim h).boundSize W + W + 13 * (W + 1) ^ 6 + 2) := by
    unfold Prim.boundSize
    norm_poly
  obtain ⟨K, D, hb⟩ := hp
  refine ⟨K * 2 ^ D, D, fun I => ?_⟩
  let W := (vecStabEnc I).wt
  have wg : (encGroup I.gs).wt < W := wt_le_wt_list (by simp [W, vecStabEnc])
  have hs := S_le_wt_encGroup I.gs
  have hn : I.n ≤ W := by nlinarith
  have hprim := (vectorStabilizerPrim h).bound_le (vecStabEnc I).size_le_wt
  have hnb := Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6)
  have hc : linVectorStabilizerCost h I ≤ (vectorStabilizerPrim h).boundSize W + W + 13 * (W + 1) ^ 6 + 2 := by
    change (vectorStabilizerPrim h).bound (vecStabEnc I) + W + 13 * (I.n + 1) ^ 6 + 2 ≤ _
    change (vectorStabilizerPrim h).bound (vecStabEnc I) ≤ (vectorStabilizerPrim h).boundSize W at hprim
    omega
  have ht := hb 0 W 0
  change (vectorStabilizerPrim h).boundSize W + W + 13 * (W + 1) ^ 6 + 2 ≤ K * (W + 0 + 0 + 2) ^ D at ht
  calc
    _ ≤ (vectorStabilizerPrim h).boundSize W + W + 13 * (W + 1) ^ 6 + 2 := hc
    _ ≤ K * (W + 2) ^ D := by simpa using ht
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
