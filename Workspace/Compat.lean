/-
Mathlib lemmas that older versions of mathlib provided and the pinned mathlib does not.
They are restated under their old names.
-/
import Mathlib.Algebra.Group.End

namespace Equiv.Perm

variable {α : Type*}

theorem inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x := f.symm_apply_apply x

theorem apply_inv_self (f : Perm α) (x : α) : f (f⁻¹ x) = x := f.apply_symm_apply x

end Equiv.Perm
