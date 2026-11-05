module

public import Mathlib.Algebra.Group.End

@[expose] public section

/-! The additive automorphisms `M ≃+ M` as a multiplicative group.

Since mathlib b63f6e8, `AddAut M` is an additive group, and `M ≃+ M` has no multiplicative group
structure. This project uses group homomorphisms `G →* (V ≃+ V)`, so this file restores the
multiplicative group that mathlib had before. Multiplication is composition in the same order
as mathlib's: `(e₁ * e₂) m = e₁ (e₂ m)`. -/
namespace GI.Impl

instance {M : Type*} [Add M] : Group (M ≃+ M) where
  mul g h := h.trans g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

@[simp] theorem addEquiv_mul_apply {M : Type*} [Add M] (e₁ e₂ : M ≃+ M) (m : M) :
    (e₁ * e₂) m = e₁ (e₂ m) := rfl

@[simp] theorem addEquiv_one_apply {M : Type*} [Add M] (m : M) :
    (1 : M ≃+ M) m = m := rfl

@[simp] theorem addEquiv_inv_apply {M : Type*} [Add M] (e : M ≃+ M) (m : M) :
    e⁻¹ m = e.symm m := rfl

end GI.Impl
