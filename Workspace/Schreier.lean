module

public import Workspace.Cited.Facts
public import Workspace.SocleOuter

@[expose] public section

/-!
# Schreier's conjecture

Schreier's conjecture says that the outer automorphism group of a finite nonabelian simple group
is solvable. This file derives it, in every universe, from the classification `GI.Cited.cfsg`
and from Schreier's conjecture for the groups on the classification list,
`GI.Cited.catalogueSchreier` (both in `Workspace/Cited/Facts.lean`).

The derivation has two steps. A finite simple group `T` in any universe is isomorphic to a group
`X` in `Type` (namely `Shrink T`). By `cfsg`, the group `X` is on the classification list, so
`catalogueSchreier` says that `Out(X)` is solvable. The isomorphism `T ≃* X` then induces a
surjection `Out(X) → Out(T)`, so `Out(T)` is solvable too.

Other files use `GI.schreier` directly.
-/

namespace GI

universe u

open SocleOuter

/-- **Schreier's conjecture.** Every finite nonabelian simple group has a solvable outer
automorphism group. -/
def SchreierConjecture : Prop :=
  ∀ (T : Type u) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Group.IsSolvable (OuterAut T)

/-- An isomorphism `T ≃* X` maps inner automorphisms of `X` to inner automorphisms of `T`, so it
induces a surjection `Out(X) → Out(T)`, and solvability passes from `Out(X)` to `Out(T)`. -/
theorem isSolvable_outerAut_of_mulEquiv {T X : Type*} [Group T] [Group X] (e : T ≃* X)
    [Group.IsSolvable (OuterAut X)] : Group.IsSolvable (OuterAut T) := by
  let φ : MulAut X →* OuterAut T :=
    (QuotientGroup.mk' (innerAut T)).comp (MulAut.congr e.symm).toMonoidHom
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (MulAut.congr e.symm).surjective
  have hinner : innerAut X ≤ φ.ker := by
    rintro _ ⟨g, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨e.symm g, ?_⟩
    apply MulEquiv.ext
    intro t
    change e.symm g * t * (e.symm g)⁻¹ = e.symm (g * e t * g⁻¹)
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  exact Group.isSolvable_of_surjective (QuotientGroup.lift_surjective_of_surjective _ φ hφ hinner)

/-- Schreier's conjecture follows from the classification and from Schreier's conjecture for the
groups on the classification list. -/
theorem schreierConjecture_of_cfsg (hcfsg : TauCeti.ClassificationStatement.{0})
    (hlist : Cited.CatalogueSchreier) : SchreierConjecture.{u} := by
  intro T _ _ _ hT
  let e : Shrink.{0} T ≃* T := Shrink.mulEquiv
  have : Finite (Shrink.{0} T) := Finite.of_equiv T e.symm.toEquiv
  have : IsSimpleGroup (Shrink.{0} T) := e.isSimpleGroup
  have hX : ∃ a b : Shrink.{0} T, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hT
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h
  have : Group.IsSolvable (OuterAut (Shrink.{0} T)) :=
    hlist (Shrink.{0} T) hX (TauCeti.classificationStatement_iff.1 hcfsg (Shrink.{0} T))
  exact isSolvable_outerAut_of_mulEquiv e.symm

/-- **Schreier's conjecture**, from `GI.Cited.cfsg` and `GI.Cited.catalogueSchreier`. -/
theorem schreier : SchreierConjecture.{u} :=
  schreierConjecture_of_cfsg Cited.cfsg Cited.catalogueSchreier

end GI
