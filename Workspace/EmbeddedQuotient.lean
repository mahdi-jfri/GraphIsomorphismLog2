module

public import Workspace.KernelQuotientFacts

@[expose] public section

namespace GI.EmbeddedQuotient

variable {G Q V Y E : Type*} [Group G] [Group Q] [MulAction G V] [MulAction Q Y]
variable {φ : G →* Q}

def top (P : Subgroup Q) : P.comap φ →* P where
  toFun g := ⟨φ g.val, g.property⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' g h := Subtype.ext (map_mul φ g.val h.val)

theorem top_onto (P : Subgroup Q) (onto : Function.Surjective φ) :
    Function.Surjective (top (φ := φ) P) := by
  rintro ⟨q, hq⟩
  obtain ⟨g, rfl⟩ := onto q
  exact ⟨⟨g, hq⟩, rfl⟩

variable (f : StabilizerQuotient.KernelQuotient φ V Y) (e : E ↪ Y)

abbrev Physical := {x : V // f.map x ∈ Set.range e}

noncomputable def map : Physical f e → E := fun x =>
  (Equiv.ofInjective e e.injective).symm ⟨f.map x.val, x.property⟩

theorem embed_map (x : Physical f e) : e (map f e x) = f.map x.val := by
  exact congrArg Subtype.val ((Equiv.ofInjective e e.injective).apply_symm_apply
    ⟨f.map x.val, x.property⟩)

theorem map_onto : Function.Surjective (map f e) := by
  intro u
  obtain ⟨x, hx⟩ := f.onto (e u)
  refine ⟨⟨x, hx.symm ▸ Set.mem_range_self u⟩, ?_⟩
  apply e.injective
  rw [embed_map]
  exact hx

variable (P : Subgroup Q) (τ : P →* Equiv.Perm E)
variable (equivariant : ∀ p u, e (τ p u) = (p : Q) • e u)

def move (g : P.comap φ) (x : Physical f e) : Physical f e :=
  ⟨g.val • x.val, by
    obtain ⟨u, hu⟩ := x.property
    refine ⟨τ (top P g) u, ?_⟩
    rw [equivariant, hu, f.equivariant]
    rfl⟩

def action : P.comap φ →* Equiv.Perm (Physical f e) where
  toFun g :=
    { toFun := move f e P τ equivariant g
      invFun := move f e P τ equivariant g⁻¹
      left_inv x := by apply Subtype.ext; exact inv_smul_smul g.val x.val
      right_inv x := by apply Subtype.ext; exact smul_inv_smul g.val x.val }
  map_one' := by ext x; exact one_smul G x.val
  map_mul' g h := by ext x; exact mul_smul g.val h.val x.val

def ideal : P.comap φ →* Equiv.Perm E := τ.comp (top P)

theorem map_equivariant (g : P.comap φ) (x : Physical f e) :
    map f e (action f e P τ equivariant g x) = ideal P τ g (map f e x) := by
  apply e.injective
  rw [embed_map]
  change f.map (g.val • x.val) = e (τ (top P g) (map f e x))
  rw [f.equivariant, equivariant, embed_map]
  rfl

theorem ideal_range (onto : Function.Surjective φ) :
    (ideal (φ := φ) P τ).range = τ.range := by
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨top P g, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨g, rfl⟩ := top_onto P onto p
    exact ⟨g, rfl⟩

end GI.EmbeddedQuotient
