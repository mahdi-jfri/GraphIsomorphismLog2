module

public import Workspace.PrimitiveAbelianExponent
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite

@[expose] public section

namespace GI.PrimitiveStructure

/-- A finite abelian group of prime exponent has actual vector-space
coordinates over the prime field, constructed from a finite basis. -/
theorem coordinates_of_prime_exponent {N : Type*} [Group N] [Finite N]
    (comm : ∀ x y : N, x * y = y * x) {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : N, x ^ p = 1) :
    ∃ d : ℕ, Nonempty (N ≃* Multiplicative (Fin d → ZMod p)) := by
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := comm }
  letI : Fact p.Prime := ⟨hp⟩
  letI nModule : Module (ZMod p) (Additive N) := AddCommGroup.zmodModule (fun x => by
    change Additive.ofMul (x.toMul ^ p) = Additive.ofMul 1
    exact congrArg Additive.ofMul (hexp x.toMul))
  letI nFinite : Module.Finite (ZMod p) (Additive N) := Module.Finite.of_finite
  letI nFree : Module.Free (ZMod p) (Additive N) :=
    Module.Free.of_divisionRing (K := ZMod p) (V := Additive N)
  let b : Module.Basis (Fin (Module.finrank (ZMod p) (Additive N))) (ZMod p) (Additive N) :=
    @Module.finBasis (ZMod p) (Additive N) _ _ nModule nFree _ nFinite
  exact ⟨Module.finrank (ZMod p) (Additive N),
    ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩⟩

/-- Primitive action hypotheses alone, together with a nontrivial abelian
normal subgroup, provide the prime field and concrete coordinates needed
by the affine-action construction. No affine representation is assumed. -/
theorem abelian_normal_coordinates {G V : Type*} [Group G] [Finite G]
    [MulAction G V] [FaithfulSMul G V] [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V) :
    ∃ p : ℕ, p.Prime ∧ ∃ d : ℕ, Nonempty (N ≃* Multiplicative (Fin d → ZMod p)) := by
  obtain ⟨p, hp, hexp⟩ := abelian_normal_prime_exponent N hne comm a
  exact ⟨p, hp, coordinates_of_prime_exponent comm hp hexp⟩

end GI.PrimitiveStructure
