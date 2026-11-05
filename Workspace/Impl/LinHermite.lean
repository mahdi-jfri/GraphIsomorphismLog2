module

public import Workspace.Impl.LinBackSub
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

/-! Reducing a full-rank rectangular row equation to the square Hermite block.
The algorithm returns a lift in the original relation rows. No oracle for row
equations or for rectangular Smith forms is assumed. -/
namespace GI.Impl
open Matrix GI.Cited

/-- The square block at the top of a rectangular Hermite form. -/
def linHermiteBlock {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ) :
    Matrix (Fin c) (Fin c) ℤ := fun i j => H (Fin.castLE hcr i) j

/-- Extend a coefficient vector by zero below the square block. -/
def linPad {r c : ℕ} (y : Fin c → ℤ) : Fin r → ℤ :=
  fun i => if hi : i.val < c then y ⟨i.val, hi⟩ else 0

/-- The bottom rows contribute zero to every row equation. -/
theorem linTopRows {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ)
    (hH : IsHermiteForm H) (y : Fin r → ℤ) :
    y ᵥ* H = (fun i => y (Fin.castLE hcr i)) ᵥ* linHermiteBlock hcr H := by
  classical
  funext j
  change ∑ i : Fin r, y i * H i j = ∑ i : Fin c, y (Fin.castLE hcr i) * H (Fin.castLE hcr i) j
  have hs : (∑ i ∈ Finset.univ.image (Fin.castLE hcr), y i * H i j) =
      ∑ i : Fin c, y (Fin.castLE hcr i) * H (Fin.castLE hcr i) j :=
    Finset.sum_image (by intro a _ b _ hab; exact Fin.castLE_injective hcr hab)
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hci : c ≤ i.val := by
    by_contra hlt
    have hi' : i.val < c := by omega
    apply hi
    exact Finset.mem_image.mpr ⟨⟨i.val, hi'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [hH.1 i j (by omega), mul_zero]

/-- Extending a block solution by zero solves the rectangular Hermite equation. -/
theorem linPadEquation {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ)
    (hH : IsHermiteForm H) (y : Fin c → ℤ) :
    linPad (r := r) y ᵥ* H = y ᵥ* linHermiteBlock hcr H := by
  rw [linTopRows hcr H hH]
  congr 1
  funext i
  simp [linPad, i.isLt]

/-- The Hermite block satisfies the hypotheses of exact triangular substitution. -/
theorem linHermiteBlock_tri {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ)
    (hH : IsHermiteForm H) :
    (∀ i j, j < i → linHermiteBlock hcr H i j = 0) ∧
      ∀ i, 0 < linHermiteBlock hcr H i i :=
  ⟨fun _ _ hij => hH.1 _ _ hij, fun _ => hH.2.1 _ _ rfl⟩

/-- In particular this is legal input to the square Smith task. -/
theorem linHermiteBlock_det_ne {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ)
    (hH : IsHermiteForm H) : (linHermiteBlock hcr H).det ≠ 0 := by
  have ht := linHermiteBlock_tri hcr H hH
  rw [Matrix.det_of_upperTriangular (M := linHermiteBlock hcr H) ht.1]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (ht.2 i)

/-- Exact substitution on the Hermite block, followed by the explicit lift yU. -/
def linHermiteSolve {r c : ℕ} (hcr : c ≤ r) (U : Matrix (Fin r) (Fin r) ℤ)
    (H : Matrix (Fin r) (Fin c) ℤ) (w : Fin c → ℤ) : Option (Fin r → ℤ) :=
  (linUpperSolve c (linHermiteBlock hcr H) w).map (fun y => linPad y ᵥ* U)

/-- Every returned vector solves the original row equation. -/
theorem linHermiteSolve_sound {r c : ℕ} (hcr : c ≤ r) (M H : Matrix (Fin r) (Fin c) ℤ)
    (U : Matrix (Fin r) (Fin r) ℤ) (h : U * M = H) (hH : IsHermiteForm H)
    (w : Fin c → ℤ) (z : Fin r → ℤ) (hz : linHermiteSolve hcr U H w = some z) :
    z ᵥ* M = w := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hz
  apply linRowLift h
  rw [linPadEquation hcr H hH]
  exact linUpperSolve_sound c _ (linHermiteBlock_tri hcr H hH).1 w y hy

/-- Failure means that the original equation has no integer solution, and conversely. -/
theorem linHermiteSolve_none_iff {r c : ℕ} (hcr : c ≤ r)
    (M H : Matrix (Fin r) (Fin c) ℤ) (U : Matrix (Fin r) (Fin r) ℤ)
    (hU : IsUnit U.det) (h : U * M = H) (hH : IsHermiteForm H) (w : Fin c → ℤ) :
    linHermiteSolve hcr U H w = none ↔ ¬ ∃ z, z ᵥ* M = w := by
  unfold linHermiteSolve
  rw [Option.map_eq_none_iff, linUpperSolve_none_iff c _
    (linHermiteBlock_tri hcr H hH).1 (fun i => ne_of_gt ((linHermiteBlock_tri hcr H hH).2 i))]
  apply not_congr
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨linPad y ᵥ* U, linRowLift h (by rw [linPadEquation hcr H hH, hy])⟩
  · intro hz
    obtain ⟨y, hy⟩ := (linRowEquation_iff M U hU w).mp hz
    rw [h, linTopRows hcr H hH] at hy
    exact ⟨_, hy⟩

/-- All kernel vectors come from coefficients on the bottom rows of U.
Together with linHermiteKernelBottom, this proves that those rows generate the kernel. -/
theorem linHermiteKernel_iff {r c : ℕ} (hcr : c ≤ r)
    (M H : Matrix (Fin r) (Fin c) ℤ) (U : Matrix (Fin r) (Fin r) ℤ)
    (hU : IsUnit U.det) (h : U * M = H) (hH : IsHermiteForm H) (z : Fin r → ℤ) :
    z ᵥ* M = 0 ↔ ∃ y : Fin r → ℤ,
      z = y ᵥ* U ∧ ∀ i : Fin c, y (Fin.castLE hcr i) = 0 := by
  constructor
  · intro hz
    let y := z ᵥ* U⁻¹
    have hzy : z = y ᵥ* U := by
      simp only [y, vecMul_vecMul, U.nonsing_inv_mul hU, vecMul_one]
    have hyH : y ᵥ* H = 0 := by
      rw [← h, ← vecMul_vecMul, ← hzy, hz]
    rw [linTopRows hcr H hH] at hyH
    have hy0 := (linHermiteBlock hcr H).eq_zero_of_vecMul_eq_zero
      (linHermiteBlock_det_ne hcr H hH) hyH
    exact ⟨y, hzy, fun i => congrFun hy0 i⟩
  · rintro ⟨y, rfl, hy⟩
    rw [vecMul_vecMul, h, linTopRows hcr H hH]
    have hz : (fun i : Fin c => y (Fin.castLE hcr i)) = 0 := funext hy
    rw [hz, zero_vecMul]

/-- Form the square nonsingular Smith input directly from a Hermite output. -/
def linHermiteSmithInst {r c : ℕ} (hc : 0 < c) (hcr : c ≤ r)
    (H : Matrix (Fin r) (Fin c) ℤ) (hH : IsHermiteForm H) : NonsingularInst :=
  ⟨c, hc, linHermiteBlock hcr H, linHermiteBlock_det_ne hcr H hH⟩

end GI.Impl
