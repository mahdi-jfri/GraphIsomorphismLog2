module

public import Workspace.Transport

@[expose] public section

namespace GI

variable {V W C : Type*}

/-- Exactness of pulling colors back along a surjective equivariant quotient map. -/
theorem pullback_transport_iff (f : V → W) (hf : Function.Surjective f)
    (p : Equiv.Perm V) (q : Equiv.Perm W)
    (equivariant : ∀ v, f (p v) = q (f v)) (x y : W → C) :
    Transports (x ∘ f) (y ∘ f) p ↔ Transports x y q := by
  constructor
  · intro h w
    obtain ⟨v, rfl⟩ := hf w
    simpa [Function.comp_def, equivariant] using h v
  · intro h v
    simpa [Function.comp_def, equivariant] using h (f v)

/-- Projecting the entire physical answer gives the entire ideal answer when every ideal
permutation has a permitted lift. This does not construct the paper's rectangle orbit. -/
theorem projected_transporter (f : V → W) (hf : Function.Surjective f)
    (G : Subgroup (Equiv.Perm V)) (P : Subgroup (Equiv.Perm W))
    (project : Equiv.Perm V → Equiv.Perm W)
    (maps : ∀ p ∈ G, project p ∈ P)
    (lifts : ∀ q ∈ P, ∃ p ∈ G, project p = q)
    (equivariant : ∀ p ∈ G, ∀ v, f (p v) = project p (f v)) (x y : W → C) :
    project '' transporter G (x ∘ f) (y ∘ f) = transporter P x y := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨maps p hp.1,
      (pullback_transport_iff f hf p (project p) (equivariant p hp.1) x y).1 hp.2⟩
  · intro hq
    obtain ⟨p, hp, heq⟩ := lifts q hq.1
    refine ⟨p, ⟨hp, ?_⟩, heq⟩
    apply (pullback_transport_iff f hf p (project p) (equivariant p hp) x y).2
    simpa [heq] using hq.2

end GI
