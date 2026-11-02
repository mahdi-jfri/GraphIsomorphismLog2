import Workspace.Impl.LinPresentationKernel
import Workspace.Lang.Lib.LinIntVector

/-! Appending integer relation rows and its exact presentation meaning. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linRowStack {r s c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (C : Matrix (Fin s) (Fin c) ℤ) :
    Matrix (Fin (r + s)) (Fin c) ℤ := Fin.addCases M C

theorem linRowStack_range {r s c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (C : Matrix (Fin s) (Fin c) ℤ) :
    Set.range (linRowStack M C) = Set.range M ∪ Set.range C := by
  ext row
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simp [linRowStack]⟩
    | right j => exact Or.inr ⟨j, by simp [linRowStack]⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨i.castAdd s, by simp [linRowStack]⟩
    · exact ⟨Fin.natAdd r j, by simp [linRowStack]⟩

theorem linRelations_stack {r s c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (C : Matrix (Fin s) (Fin c) ℤ) :
    linRelations (linRowStack M C) = linRelations M ⊔ linRelations C := by
  simp only [linRelations, range_vecMulLinear]
  change Submodule.span ℤ (Set.range (linRowStack M C)) =
    Submodule.span ℤ (Set.range M) ⊔ Submodule.span ℤ (Set.range C)
  rw [linRowStack_range, Submodule.span_union]

/-- The matrix encoding stacks rows by the existing list append operation. -/
theorem linRowStack_value {r s c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (C : Matrix (Fin s) (Fin c) ℤ) :
    encIntMatrix (linRowStack M C) =
      .list (((List.finRange r).map fun i => linVecVal (M i)) ++
        ((List.finRange s).map fun j => linVecVal (C j))) := by
  apply congrArg Val.list
  simp only [← List.ofFn_eq_map, List.ofFn_add, linRowStack]
  simp [Fin.addCases, linVecVal, ← List.ofFn_eq_map]
  all_goals rfl

/-- Appending subgroup coordinate generators forms precisely the quotient by
their images, through the original coordinate map. -/
noncomputable def linPresentationStackEquiv {n s : ℕ} {Q : Type*} [AddCommGroup Q]
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0)
    (f : (Fin n → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Matrix (Fin s) (Fin n) ℤ) :
    ((Fin n → ℤ) ⧸ linRelations (linRowStack M C)) ≃ₗ[ℤ] (Q ⧸ (linRelations C).map f) := by
  have he : linRelations (linRowStack M C) = LinearMap.ker f ⊔ linRelations C := by
    rw [linRelations_stack, linPresentation_ker_eq M hM f hf hrel hcard]
  exact (Submodule.quotEquivOfEq _ _ he).trans (linPresentationExtendEquiv f hf (linRelations C))

@[simp] theorem linPresentationStackEquiv_mk {n s : ℕ} {Q : Type*} [AddCommGroup Q]
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0)
    (f : (Fin n → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs)
    (C : Matrix (Fin s) (Fin n) ℤ) (z : Fin n → ℤ) :
    linPresentationStackEquiv M hM f hf hrel hcard C ((linRelations (linRowStack M C)).mkQ z) =
      ((linRelations C).map f).mkQ (f z) := rfl

end GI.Impl
