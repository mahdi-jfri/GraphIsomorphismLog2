import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Exact string transporters. Mathlib permutations compose as functions:
`(p * q) v = p (q v)`. Thus a source-automorphism coset is written `t * a`,
the reverse of the paper's right-action notation `a t`. -/
namespace GI

variable {V C : Type*}

def Transports (x y : V → C) (p : Equiv.Perm V) : Prop :=
  ∀ v, y (p v) = x v

@[simp] theorem transports_one (x : V → C) : Transports x x 1 := by
  intro v; rfl

theorem Transports.comp {x y z : V → C} {p q : Equiv.Perm V}
    (hp : Transports x y p) (hq : Transports y z q) :
    Transports x z (q * p) := by
  intro v
  exact (hq (p v)).trans (hp v)

theorem Transports.inv {x y : V → C} {p : Equiv.Perm V}
    (hp : Transports x y p) : Transports y x p⁻¹ := by
  intro v
  simpa using (hp (p⁻¹ v)).symm

def automorphisms (G : Subgroup (Equiv.Perm V)) (x : V → C) :
    Subgroup (Equiv.Perm V) where
  carrier := {p | p ∈ G ∧ Transports x x p}
  one_mem' := ⟨G.one_mem, transports_one x⟩
  mul_mem' := fun hp hq => ⟨G.mul_mem hp.1 hq.1, hq.2.comp hp.2⟩
  inv_mem' := fun hp => ⟨G.inv_mem hp.1, hp.2.inv⟩

def transporter (G : Subgroup (Equiv.Perm V)) (x y : V → C) :
    Set (Equiv.Perm V) := {p | p ∈ G ∧ Transports x y p}

theorem transporter_coset (G : Subgroup (Equiv.Perm V)) (x y : V → C)
    {t : Equiv.Perm V} (ht : t ∈ transporter G x y) :
    transporter G x y = {p | ∃ a ∈ automorphisms G x, p = t * a} := by
  ext p
  constructor
  · intro hp
    refine ⟨t⁻¹ * p, ⟨G.mul_mem (G.inv_mem ht.1) hp.1, hp.2.comp ht.2.inv⟩, ?_⟩
    simp
  · rintro ⟨a, ha, rfl⟩
    exact ⟨G.mul_mem ht.1 ha.1, ha.2.comp ht.2⟩

/-- Intersecting exact constraints one at a time loses no candidate. -/
theorem transport_pair (x y : V → C) {D : Type*} (u v : V → D)
    (p : Equiv.Perm V) :
    Transports (fun a => (x a, u a)) (fun a => (y a, v a)) p ↔
      Transports x y p ∧ Transports u v p := by
  constructor
  · intro h
    exact ⟨fun a => congrArg Prod.fst (h a), fun a => congrArg Prod.snd (h a)⟩
  · rintro ⟨h, k⟩ a
    exact Prod.ext (h a) (k a)

/-- An exhaustive family of overcosets becomes exact after original constraints are checked.
No claim that an arbitrary union of cosets is a coset is used. -/
theorem exact_branch_union {P : Type*} {ι : Type*} (valid : Set P)
    (branch : ι → Set P) (covers : ∀ p ∈ valid, ∃ i, p ∈ branch i) :
    {p | ∃ i, p ∈ branch i ∧ p ∈ valid} = valid := by
  ext p
  constructor
  · rintro ⟨_, _, hp⟩; exact hp
  · intro hp
    obtain ⟨i, hi⟩ := covers p hp
    exact ⟨i, hi, hp⟩

end GI
