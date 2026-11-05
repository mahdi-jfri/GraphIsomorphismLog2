module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

@[expose] public section

/-!
# Cited inputs: the classification of finite simple groups, and Schreier's conjecture

The paper uses the classification of finite simple groups (CFSG) through two consequences:
Schreier's conjecture and Maróti's theorem on primitive groups (`GI.Cited.MarotiPrimitive`).
This file states the first two inputs in the form of AxiomMath's CFSG formalization
(https://github.com/AxiomMath/CFSG), and `Workspace/Cited/Facts.lean` proves them from it.

* **CFSG** is `TauCeti.ClassificationStatement`, the statement that AxiomMath proves: every finite
  simple group is isomorphic to one of the explicitly constructed groups indexed by
  `TauCeti.CFSGIndex` (cyclic groups of prime order, alternating groups, groups of Lie type and
  sporadic groups).
* **Schreier's conjecture for the list** is `GI.Cited.CatalogueSchreier` below: every nonabelian
  simple group on that list has a solvable outer automorphism group. It is the body of AxiomMath's
  `CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier`, which AxiomMath proves as
  `catalogueSchreier_of_certificates` (`CFSG/Yardstones/Md42047359a2a/Reduction.lean`). The
  definitions `catalogueInner`, `CatalogueOuter` and `InCatalog` are copies of AxiomMath's
  `CFSG.ComponentClassification.OuterAutomorphisms.inner`, `...OuterAutomorphisms.Outer` and
  `CFSG.Assembly.InCatalog`, with the same bodies.

Together they give Schreier's conjecture for every finite nonabelian simple group
(`GI.schreierConjecture_of_cfsg` in `Workspace/Schreier.lean`).
-/

namespace GI.Cited

/-- The inner automorphisms of `G`: the image of conjugation. A copy of AxiomMath's
`CFSG.ComponentClassification.OuterAutomorphisms.inner`. -/
def catalogueInner (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

instance catalogueInner_normal (G : Type*) [Group G] : (catalogueInner G).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ a
  refine ⟨a g, ?_⟩
  apply MulEquiv.ext
  intro x
  change a g * x * (a g)⁻¹ = a (g * a.symm x * g⁻¹)
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- The outer automorphism group `Aut(G)/Inn(G)`. A copy of AxiomMath's
`CFSG.ComponentClassification.OuterAutomorphisms.Outer`. -/
abbrev CatalogueOuter (G : Type*) [Group G] := MulAut G ⧸ catalogueInner G

/-- `G` is isomorphic to a group on the classification list. A copy of AxiomMath's
`CFSG.Assembly.InCatalog`. -/
def InCatalog (G : Type) [Group G] : Prop :=
  ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group)

/-- **Schreier's conjecture for the classification list.** Every nonabelian simple group that is
isomorphic to a group on the list has a solvable outer automorphism group.

*Source.* The body of AxiomMath's `CFSG.ComponentClassification.CatalogueRelativeB.
CatalogueSchreier`, proved there as `catalogueSchreier_of_certificates`. For the alternating groups
`Out(Alt(n))` has order 2 for `n ≠ 6` and order 4 for `n = 6`; for the sporadic groups it has
order 1 or 2; for a group of Lie type it is an extension of the diagonal automorphisms by field
and graph automorphisms, and is solvable (Steinberg's theorem on automorphisms of Chevalley
groups).

*Edge cases.* Cyclic groups of prime order are excluded by the hypothesis that `X` is not
abelian. -/
def CatalogueSchreier : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
    (∃ a b : X, a * b ≠ b * a) → InCatalog X →
      Group.IsSolvable (CatalogueOuter X)

end GI.Cited
