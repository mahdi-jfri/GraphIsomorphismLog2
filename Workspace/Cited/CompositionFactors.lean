module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Composition series and the products `a(X)`, `b(X)`

[GMP, Section 1] (Guralnick, Maróti, Pyber, *Normalizers of primitive permutation groups*,
Adv. Math. 310 (2017) 1017-1063; arXiv:1603.00187v2, p. 3): "for a finite group `X` we denote
the product of the orders of the abelian and the nonabelian composition factors of a
composition series for `X` by `a(X)` and `b(X)` respectively." The paper (Appendix A,
subsubsection "A radical-free order bound and its constructive use") uses the same symbols.

`CompositionProducts X a b` says: `X` has a composition series whose abelian factors have
orders with product `a` and whose nonabelian factors have orders with product `b`. It is
defined by recursion on the top of the series. A composition series of `X` is either empty
(`X` trivial), or a normal subgroup `K` of `X` with `X/K` simple, followed by a composition
series of `K`.

This file only defines the predicate; it is used by the statements of the cited results in
`Workspace/Cited/GMP.lean`. The Jordan-Hölder uniqueness (`a` and `b` do not depend on the
series) and the existence of a series for finite groups are proved in
`Workspace/CompositionFactors.lean`.
-/

namespace GI.Cited

universe u

/-- `CompositionProducts X a b`: the group `X` has a composition series in which the product
of the orders of the abelian factors is `a` and the product of the orders of the nonabelian
factors is `b`. -/
inductive CompositionProducts : (X : Type u) → [Group X] → ℕ → ℕ → Prop
  /-- The trivial group has the empty series. -/
  | trivial (X : Type u) [Group X] [Subsingleton X] : CompositionProducts X 1 1
  /-- A simple abelian top factor `X/K` adds its order to `a`. -/
  | abelianTop (X : Type u) [Group X] (K : Subgroup X) [K.Normal] (a b : ℕ) :
      IsSimpleGroup (X ⧸ K) → (∀ x y : X ⧸ K, x * y = y * x) →
      CompositionProducts K a b → CompositionProducts X (a * Nat.card (X ⧸ K)) b
  /-- A simple nonabelian top factor `X/K` adds its order to `b`. -/
  | nonabelianTop (X : Type u) [Group X] (K : Subgroup X) [K.Normal] (a b : ℕ) :
      IsSimpleGroup (X ⧸ K) → ¬ (∀ x y : X ⧸ K, x * y = y * x) →
      CompositionProducts K a b → CompositionProducts X a (b * Nat.card (X ⧸ K))

end GI.Cited
