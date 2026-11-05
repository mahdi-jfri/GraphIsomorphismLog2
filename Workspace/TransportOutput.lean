module

public import Workspace.Pullback
public import Mathlib.Algebra.Group.Subgroup.Map

@[expose] public section

namespace GI.TransportOutput

variable {V W C : Type*}

def aut (G : Subgroup (Equiv.Perm V)) (x : V → C) : Subgroup G :=
  (automorphisms G x).comap G.subtype

@[simp] theorem mem_aut (G : Subgroup (Equiv.Perm V)) (x : V → C) (g : G) :
    g ∈ aut G x ↔ Transports x x g.val :=
  and_iff_right g.property

/-- A finite generating list and one representative describe the whole
nonempty transporter. The list is not required to enumerate the group. -/
structure Solution (G : Subgroup (Equiv.Perm V)) (x y : V → C) where
  representative : G
  transports : Transports x y representative.val
  generators : List G
  generates : Subgroup.closure {g : G | g ∈ generators} = aut G x

inductive Answer (G : Subgroup (Equiv.Perm V)) (x y : V → C)
  | empty (certificate : ∀ g : G, ¬ Transports x y g.val)
  | nonempty (solution : Solution G x y)

theorem full_coset {G : Subgroup (Equiv.Perm V)} {x y : V → C}
    (s : Solution G x y) (g : G) :
    Transports x y g.val ↔ ∃ a : G,
      a ∈ Subgroup.closure {h : G | h ∈ s.generators} ∧ g = s.representative * a := by
  rw [s.generates]
  constructor
  · intro hg
    refine ⟨s.representative⁻¹ * g, ?_, by simp⟩
    rw [mem_aut]
    exact hg.comp s.transports.inv
  · rintro ⟨a, ha, rfl⟩
    exact ((mem_aut G x a).mp ha).comp s.transports

variable {G : Subgroup (Equiv.Perm V)} {K : Subgroup (Equiv.Perm W)}
variable (π : G →* K) (surjective : Function.Surjective π)
variable (f : V → W) (onto : Function.Surjective f)
variable (equivariant : ∀ (g : G) v, f (g.val v) = (π g).val (f v))

include surjective onto equivariant in
theorem map_aut (x : W → C) :
    (aut G (x ∘ f)).map π = aut K x := by
  ext k
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g ∈ aut G (x ∘ f) at hg
    rw [mem_aut] at hg ⊢
    exact (pullback_transport_iff f onto g.val (π g).val (equivariant g) x x).mp hg
  · intro hk
    obtain ⟨g, rfl⟩ := surjective k
    refine ⟨g, ?_, rfl⟩
    change g ∈ aut G (x ∘ f)
    rw [mem_aut] at hk ⊢
    exact (pullback_transport_iff f onto g.val (π g).val (equivariant g) x x).mpr hk

def projectSolution {x y : W → C} (s : Solution G (x ∘ f) (y ∘ f)) : Solution K x y where
  representative := π s.representative
  transports := (pullback_transport_iff f onto s.representative.val _
    (equivariant s.representative) x y).mp s.transports
  generators := s.generators.map π
  generates := by
    have hs : {k : K | k ∈ s.generators.map π} = π '' {g : G | g ∈ s.generators} := by
      ext k
      simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
    rw [hs, ← MonoidHom.map_closure, s.generates]
    exact map_aut π surjective f onto equivariant x

theorem projectSolution_length {x y : W → C} (s : Solution G (x ∘ f) (y ∘ f)) :
    (projectSolution π surjective f onto equivariant s).generators.length = s.generators.length :=
  List.length_map π

def projectAnswer {x y : W → C} (a : Answer G (x ∘ f) (y ∘ f)) : Answer K x y :=
  match a with
  | .empty certificate => .empty (by
      intro k hk
      obtain ⟨g, rfl⟩ := surjective k
      exact certificate g ((pullback_transport_iff f onto g.val _ (equivariant g) x y).mpr hk))
  | .nonempty s => .nonempty (projectSolution π surjective f onto equivariant s)

end GI.TransportOutput
