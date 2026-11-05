module

public import Workspace.EmbeddedQuotient
public import Workspace.OrbitBudget

@[expose] public section

namespace GI.EmbeddedQuotient

variable {Q V Y E : Type*} [Group Q] [MulAction Q Y]
variable (G : Subgroup (Equiv.Perm V)) (φ : G →* Q) (P : Subgroup Q)

def physicalSubgroup : Subgroup (Equiv.Perm V) := (P.comap φ).map G.subtype

theorem physicalSubgroup_le : physicalSubgroup G φ P ≤ G := by
  rintro p ⟨g, _, rfl⟩
  exact g.property

noncomputable def physicalEquiv : P.comap φ ≃* physicalSubgroup G φ P :=
  (P.comap φ).equivMapOfInjective G.subtype Subtype.val_injective

variable (f : StabilizerQuotient.KernelQuotient φ V Y) (e : E ↪ Y)
variable (τ : P →* Equiv.Perm E)
variable (equivariant : ∀ p u, e (τ p u) = (p : Q) • e u)

noncomputable def cover (x : Physical f e) :
    ActionCover (physicalSubgroup G φ P) x.val x where
  project := (action f e P τ equivariant).comp (physicalEquiv G φ P).symm.toMonoidHom
  embed := ⟨Subtype.val, Subtype.val_injective⟩
  base := rfl
  equivariant h y := by
    have he := congrArg Subtype.val ((physicalEquiv G φ P).apply_symm_apply h)
    exact congrArg (fun p : Equiv.Perm V => p y.val) he

theorem cover_range (x : Physical f e) :
    (cover G φ P f e τ equivariant x).project.range = (action f e P τ equivariant).range := by
  ext p
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨(physicalEquiv G φ P).symm h, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨physicalEquiv G φ P h, ?_⟩
    change action f e P τ equivariant ((physicalEquiv G φ P).symm (physicalEquiv G φ P h)) = _
    rw [MulEquiv.symm_apply_apply]

variable [Fintype V] [Fintype (Physical f e)]

/-- Inheritance is for the faithful restriction of the actual preimage subgroup.
No budget bound on the ideal action is assumed. -/
theorem physical_budget_le {cutoff : ℕ} (hcutoff : 5 ≤ cutoff) (x : Physical f e) :
    sigma cutoff x (action f e P τ equivariant).range ≤ sigma cutoff x.val G := by
  rw [← cover_range G φ P f e τ equivariant x,
    ← (cover G φ P f e τ equivariant x).sigma_eq cutoff]
  exact sigma_subgroup_mono hcutoff x.val (physicalSubgroup_le G φ P)

end GI.EmbeddedQuotient
