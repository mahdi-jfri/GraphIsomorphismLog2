module

public import Workspace.ActiveLocalization

@[expose] public section

namespace GI

variable {A D : Type*} [Group A]

/-- Pointwise kernel on the active orbit in a supplied permutation action. -/
def actionOrbitKernel (p : A →* Equiv.Perm D) (a : D) : Subgroup A :=
  letI : MulAction A D := MulAction.compHom D p
  (MulAction.toPermHom A (MulAction.orbit A a)).ker

instance actionOrbitKernel_normal (p : A →* Equiv.Perm D) (a : D) :
    (actionOrbitKernel p a).Normal := MonoidHom.normal_ker _

theorem mem_actionOrbitKernel_iff (p : A →* Equiv.Perm D) (a : D) (h : A) :
    h ∈ actionOrbitKernel p a ↔ ∀ g : A, p h (p g a) = p g a := by
  letI : MulAction A D := MulAction.compHom D p
  constructor
  · intro hh g
    have heq := congrArg (fun e : Equiv.Perm (MulAction.orbit A a) =>
      (e ⟨g • a, ⟨g, rfl⟩⟩).val) hh
    exact heq
  · intro hh
    apply Equiv.ext
    intro x
    obtain ⟨g, hg⟩ := x.property
    apply Subtype.ext
    change p h x.val = x.val
    change p g a = x.val at hg
    rw [← hg]
    exact hh g

end GI
