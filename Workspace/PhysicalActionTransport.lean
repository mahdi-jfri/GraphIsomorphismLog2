import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Action.End

namespace GI.PhysicalTransport

variable {H G V : Type*} [Group H] [Group G] [MulAction H V]

/-- Transport the acting group, preserving every point of the original
physical domain. -/
def action (e : H ≃* G) : MulAction G V := MulAction.compHom V e.symm.toMonoidHom

theorem preprimitive (e : H ≃* G) [MulAction.IsPreprimitive H V] :
    letI := action (V := V) e
    MulAction.IsPreprimitive G V := by
  letI := action (V := V) e
  let f : V →ₑ[e.toMonoidHom] V :=
    { toFun := id
      map_smul' := by
        intro h v
        change h • v = e.symm (e h) • v
        rw [e.symm_apply_apply] }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- The transported action has exactly the same physical permutation
image, so no relabeling or degree assumption is hidden in the transport. -/
theorem image_eq (e : H ≃* G) :
    letI := action (V := V) e
    (MulAction.toPermHom G V).range = (MulAction.toPermHom H V).range := by
  letI := action (V := V) e
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨e.symm g, ?_⟩
    apply Equiv.ext
    intro v
    rfl
  · rintro ⟨h, rfl⟩
    refine ⟨e h, ?_⟩
    apply Equiv.ext
    intro v
    change e.symm (e h) • v = h • v
    rw [e.symm_apply_apply]

end GI.PhysicalTransport
