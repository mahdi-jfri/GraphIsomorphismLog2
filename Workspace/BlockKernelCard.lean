import Workspace.BudgetInductionBlocks
import Mathlib.GroupTheory.Index

namespace GI.BlockCover

variable {V B : Type*} {H : Subgroup (Equiv.Perm V)}

/-- The actual block-action kernel acts on each actual label fiber. -/
def kernelFiberHom (c : BlockCover H B) (b : B) :
    c.project.ker →* Equiv.Perm {x : V // c.label x = b} where
  toFun k :=
    { toFun x := ⟨(k.val : Equiv.Perm V) x.val, by
        rw [c.equivariant, x.property]
        exact congrArg (fun p : Equiv.Perm B => p b) k.property⟩
      invFun x := ⟨((k⁻¹).val : Equiv.Perm V) x.val, by
        rw [c.equivariant, x.property]
        exact congrArg (fun p : Equiv.Perm B => p b) (k⁻¹).property⟩
      left_inv x := Subtype.ext ((k.val : Equiv.Perm V).symm_apply_apply x.val)
      right_inv x := Subtype.ext ((k.val : Equiv.Perm V).apply_symm_apply x.val) }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The kernel is faithfully represented by its restrictions to all
actual fibers, since those fibers cover the original domain. -/
theorem kernelFiberHom_injective (c : BlockCover H B) :
    Function.Injective (Pi.monoidHom (c.kernelFiberHom)) := by
  intro k l he
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrArg (fun f => (f (c.label x) ⟨x, rfl⟩).val) he

variable [Fintype V] [Fintype B]

/-- The standard wreath-product order bound is derived directly from
the actual kernel and actual block permutation image. -/
theorem card_le_factorial_product (c : BlockCover H B) :
    Nat.card H ≤ (Nat.card B).factorial *
      ∏ b : B, (Nat.card {x : V // c.label x = b}).factorial := by
  classical
  have hker := Nat.card_le_card_of_injective _ (kernelFiberHom_injective c)
  rw [Nat.card_pi] at hker
  simp_rw [Nat.card_perm] at hker
  have himage := Subgroup.card_le_card_group c.project.range
  rw [Nat.card_perm] at himage
  rw [← c.project.ker.card_mul_index, Subgroup.index_ker]
  exact (Nat.mul_le_mul hker himage).trans_eq (Nat.mul_comm _ _)

/-- Transitivity derives the uniform fiber size; it is not an extra
structural hypothesis in the imprimitive order estimate. -/
theorem card_le_factorial_pow [MulAction.IsPretransitive H V]
    (c : BlockCover H B) (onto : Function.Surjective c.label) (a : V) :
    Nat.card H ≤ (Nat.card B).factorial *
      (Nat.card {x : V // c.label x = c.label a}).factorial ^ Nat.card B := by
  classical
  letI : MulAction H B := MulAction.compHom B c.project
  have ht : ∀ b d : B, ∃ h : H, h • b = d :=
    equivariant_quotient_transitive c.label onto c.equivariant (MulAction.exists_smul_eq H)
  have hf : ∀ b : B, Nat.card {x : V // c.label x = b} =
      Nat.card {x : V // c.label x = c.label a} :=
    fun b => equivariant_fiber_card_eq c.label c.equivariant ht b (c.label a)
  have hb := c.card_le_factorial_product
  simp_rw [hf] at hb
  simpa only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card] using hb

end GI.BlockCover
