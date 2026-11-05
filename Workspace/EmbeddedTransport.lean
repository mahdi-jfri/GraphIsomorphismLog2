module

public import Workspace.EmbeddedQuotient
public import Workspace.ImageTransport

@[expose] public section

namespace GI.EmbeddedQuotient

variable {G Q V Y E C : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q Y]
variable {φ : G →* Q}
variable (f : StabilizerQuotient.KernelQuotient φ V Y) (e : E ↪ Y)
variable (P : Subgroup Q) (τ : P →* Equiv.Perm E)
variable (equivariant : ∀ p u, e (τ p u) = (p : Q) • e u)

def permittedImage : P.comap φ →* τ.range := τ.rangeRestrict.comp (top P)

theorem permittedImage_onto (onto : Function.Surjective φ) :
    Function.Surjective (permittedImage (φ := φ) P τ) := by
  rintro ⟨q, p, rfl⟩
  obtain ⟨g, rfl⟩ := top_onto P onto p
  exact ⟨g, rfl⟩

theorem physical_kernel_le :
    (action f e P τ equivariant).rangeRestrict.ker ≤
      (permittedImage (φ := φ) P τ).ker := by
  intro h hh
  have hk := ImageTransport.kernel_le (action f e P τ equivariant) (ideal P τ)
    (map f e) (map_onto f e) (map_equivariant f e P τ equivariant) hh
  change permittedImage P τ h = 1
  exact Subtype.ext (congrArg (fun k : (ideal (φ := φ) P τ).range => k.val) hk)

/-- Projection from the faithful physical restriction into all permitted
coordinate permutations. It is independent of the chosen lift. -/
noncomputable def permittedProjection : (action f e P τ equivariant).range →* τ.range :=
  HomDescent.factor (action f e P τ equivariant).rangeRestrict
    (ImageTransport.range_onto _) (permittedImage P τ)
    (physical_kernel_le f e P τ equivariant)

theorem permittedProjection_apply (g : P.comap φ) :
    permittedProjection f e P τ equivariant
      ((action f e P τ equivariant).rangeRestrict g) = permittedImage P τ g :=
  HomDescent.factor_apply _ _ _ _ g

theorem permittedProjection_onto (onto : Function.Surjective φ) :
    Function.Surjective (permittedProjection f e P τ equivariant) :=
  HomDescent.factor_surjective _ _ _ _ (permittedImage_onto P τ onto)

theorem permittedProjection_equivariant
    (p : (action f e P τ equivariant).range) (x : Physical f e) :
    map f e (p.val x) = (permittedProjection f e P τ equivariant p).val (map f e x) := by
  obtain ⟨g, rfl⟩ := ImageTransport.range_onto (action f e P τ equivariant) p
  rw [permittedProjection_apply]
  exact map_equivariant f e P τ equivariant g x

/-- The entire physical transporter projects onto the entire permitted
matrix transporter. This includes both nonempty and empty answers. -/
theorem exact_permitted_transporter (onto : Function.Surjective φ) (x y : E → C) :
    permittedProjection f e P τ equivariant ''
      {p : (action f e P τ equivariant).range |
        Transports (x ∘ map f e) (y ∘ map f e) p.val} =
      {q : τ.range | Transports x y q.val} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (pullback_transport_iff (map f e) (map_onto f e) p.val _
      (permittedProjection_equivariant f e P τ equivariant p) x y).mp hp
  · intro hq
    obtain ⟨p, rfl⟩ := permittedProjection_onto f e P τ equivariant onto q
    exact ⟨p, (pullback_transport_iff (map f e) (map_onto f e) p.val _
      (permittedProjection_equivariant f e P τ equivariant p) x y).mpr hq, rfl⟩

end GI.EmbeddedQuotient
