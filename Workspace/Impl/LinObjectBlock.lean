module

public import Workspace.Impl.LinObjectQuotient
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-! The local relation matrices occupy disjoint blocks. The column order
is coordinate first, then piece, so it also covers the empty product. -/
namespace GI.Impl
open Matrix

def linObjectBlockMatrix {p r d : ℕ} (M : Fin p → Matrix (Fin r) (Fin d) ℤ) :
    Matrix (Fin (r * p)) (Fin (d * p)) ℤ :=
  (blockDiagonal M).reindex finProdFinEquiv finProdFinEquiv

@[simp] theorem linObjectBlockMatrix_apply {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (i k : Fin p) (a : Fin r) (j : Fin d) :
    linObjectBlockMatrix M (finProdFinEquiv (a, i)) (finProdFinEquiv (j, k)) =
      if i = k then M i a j else 0 := by
  simp [linObjectBlockMatrix, blockDiagonal_apply]

theorem linObjectBlockMatrix_vecMul {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (z : Fin (r * p) → ℤ)
    (i : Fin p) (j : Fin d) :
    Matrix.vecMul z (linObjectBlockMatrix M) (finProdFinEquiv (j, i)) =
      Matrix.vecMul (fun a => z (finProdFinEquiv (a, i))) (M i) j := by
  simp only [Matrix.vecMul, dotProduct]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [Fintype.sum_prod_type, mul_ite]

theorem linObjectBlockMatrix_mulVec {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (z : Fin (d * p) → ℤ)
    (i : Fin p) (a : Fin r) :
    Matrix.mulVec (linObjectBlockMatrix M) z (finProdFinEquiv (a, i)) =
      Matrix.mulVec (M i) (fun j => z (finProdFinEquiv (j, i))) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [Fintype.sum_prod_type, ite_mul]

theorem linObjectBlockMatrix_injective {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (hM : ∀ i, Function.Injective (M i).mulVec) :
    Function.Injective (linObjectBlockMatrix M).mulVec := by
  intro x y hxy
  ext k
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hi : (fun j => x (finProdFinEquiv (j, i))) =
      (fun j => y (finProdFinEquiv (j, i))) := by
    apply hM i
    ext a
    simpa only [linObjectBlockMatrix_mulVec] using congrFun hxy (finProdFinEquiv (a, i))
  exact congrFun hi j

/-- A vector lies in the block row lattice exactly when each component
lies in the corresponding local row lattice. -/
theorem linObjectBlockMatrix_relations {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (w : Fin (d * p) → ℤ) :
    (∃ z, Matrix.vecMul z (linObjectBlockMatrix M) = w) ↔
      ∀ i, ∃ z, Matrix.vecMul z (M i) = fun j => w (finProdFinEquiv (j, i)) := by
  constructor
  · rintro ⟨z, hz⟩ i
    refine ⟨fun a => z (finProdFinEquiv (a, i)), ?_⟩
    ext j
    rw [← linObjectBlockMatrix_vecMul, hz]
  · intro h
    classical
    choose z hz using h
    refine ⟨fun a => z (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm a).1, ?_⟩
    apply funext
    intro k
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [linObjectBlockMatrix_vecMul]
    simpa using congrFun (hz i) j

end GI.Impl
