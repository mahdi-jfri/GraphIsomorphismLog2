module

public import Workspace.Impl.LinPresentationExtend

@[expose] public section

/-! The determinant certificate identifies the whole relation kernel. This
is the equality used when appending the subgroup and diagonal relations. -/
namespace GI.Impl

theorem linPresentation_ker_eq {n : ℕ} {Q : Type*} [AddCommGroup Q]
    (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0)
    (f : (Fin n → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f)
    (hrel : linRelations M ≤ LinearMap.ker f) (hcard : Nat.card Q = M.det.natAbs) :
    LinearMap.ker f = linRelations M := by
  let e := linPresentationEquiv M hM f hf hrel hcard
  apply le_antisymm _ hrel
  intro z hz
  have hh : e ((linRelations M).mkQ z) = 0 := hz
  have he : e ((linRelations M).mkQ z) = e 0 := by rw [map_zero]; exact hh
  have hz0 : (linRelations M).mkQ z = 0 := e.injective he
  exact (Submodule.Quotient.mk_eq_zero _).mp hz0

end GI.Impl
