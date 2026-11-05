module

public import Workspace.OrbitBudget
public import Workspace.Pullback

@[expose] public section

namespace GI.ImageTransport

variable {H X Y C : Type*} [Group H]

theorem range_onto {A B : Type*} [Group A] [Group B] (q : A →* B) :
    Function.Surjective q.rangeRestrict := by
  rintro ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := hb
  exact ⟨a, rfl⟩

theorem kernel_le (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x)) :
    physical.rangeRestrict.ker ≤ ideal.rangeRestrict.ker := by
  intro h hh
  have hp : physical h = 1 := congrArg Subtype.val hh
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := onto y
  change ideal h (f x) = f x
  rw [← equivariant, hp]
  rfl

/-- The projection out of the faithful physical image is derived from the
actual actions and equivariant surjection. Permitted lifts are not an input. -/
noncomputable def project (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x)) :
    physical.range →* ideal.range :=
  HomDescent.factor physical.rangeRestrict (range_onto physical)
    ideal.rangeRestrict (kernel_le physical ideal f onto equivariant)

theorem project_apply (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x)) (h : H) :
    project physical ideal f onto equivariant (physical.rangeRestrict h) =
      ideal.rangeRestrict h :=
  HomDescent.factor_apply _ _ _ _ h

theorem project_onto (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x)) :
    Function.Surjective (project physical ideal f onto equivariant) :=
  HomDescent.factor_surjective _ _ _ _ (range_onto ideal)

theorem project_equivariant (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x))
    (p : physical.range) (x : X) :
    f (p.val x) = (project physical ideal f onto equivariant p).val (f x) := by
  obtain ⟨h, rfl⟩ := range_onto physical p
  rw [project_apply]
  exact equivariant h x

/-- Projecting the complete transporter on the faithful physical image gives
exactly the complete ideal-image transporter, including emptiness. -/
theorem exact_transporter (physical : H →* Equiv.Perm X) (ideal : H →* Equiv.Perm Y)
    (f : X → Y) (onto : Function.Surjective f)
    (equivariant : ∀ h x, f (physical h x) = ideal h (f x)) (x y : Y → C) :
    project physical ideal f onto equivariant ''
      {p : physical.range | Transports (x ∘ f) (y ∘ f) p.val} =
      {q : ideal.range | Transports x y q.val} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (pullback_transport_iff f onto p.val _
      (project_equivariant physical ideal f onto equivariant p) x y).mp hp
  · intro hq
    obtain ⟨p, rfl⟩ := project_onto physical ideal f onto equivariant q
    exact ⟨p, (pullback_transport_iff f onto p.val _
      (project_equivariant physical ideal f onto equivariant p) x y).mpr hq, rfl⟩

end GI.ImageTransport
