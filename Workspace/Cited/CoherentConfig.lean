import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.End

/-!
# `k`-ary configurations and coherent configurations ([H, Sections 2.3–2.4])

These definitions are used by the cited statements `GI.Cited.KaryCoherentRefinement` (below)
and `GI.Cited.DesignLemma` (`Workspace/Cited/DesignLemma.lean`). They are part of the trusted
statement.

[H] = Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*,
arXiv:1710.04574v1 (12 Oct 2017). The set `Γ` is `Fin n`. A `k`-ary partition structure is a
coloring `c : Γ^k → ℕ` of the `k`-tuples; a tuple is a function `Fin k → Fin n`. [H, Section 2]:
"we write `Ω^k` for the set of `x = (x₁, …, x_k)` with the action on the left given by
`(φ(x))_r = x_{φ(r)}`", that is, `φ(x) = x ∘ φ` for every map `φ : Fin k → Fin k`.
-/

namespace GI.Cited

open Equiv

variable {n k : ℕ}

/-- **[H, Definition 2.5].** A `k`-ary configuration: "(a) For all `x, y ∈ Γ^k`, if
`c(x) = c(y)`, then `ρ(x) = ρ(y)`. (b) There is a homomorphism of monoids
`η : M({1,…,k}) → M(C)` such that for all `τ ∈ M({1,…,k})`, `c(τ(x)) = τ^η(c(x))`,
`∀ x ∈ Γ^k`." Here `ρ(x)` is the equality pattern `i ∼ j ↔ x_i = x_j`.

Condition (b) is stated as "`c(x) = c(y)` implies `c(x ∘ τ) = c(y ∘ τ)` for every
`τ : Fin k → Fin k`". This is equivalent: given it, put `τ^η(j) = c(x ∘ τ)` for any `x` of
color `j`, and `τ^η(j) = j` for colors `j` that do not occur; this is a monoid homomorphism in
[H]'s exponent (right action) convention, since `(x ∘ τ') ∘ τ = x ∘ (τ' ∘ τ)`. -/
def IsConfiguration (c : (Fin k → Fin n) → ℕ) : Prop :=
  (∀ x y, c x = c y → ∀ i j, (x i = x j ↔ y i = y j)) ∧
  (∀ x y, c x = c y → ∀ τ : Fin k → Fin k, c (x ∘ τ) = c (y ∘ τ))

/-- **[H, Definition 2.8]** (coherence): "there is a function `γ : C^k × C → ℤ_{≥0}` such that,
for arbitrary `κ ∈ C^k` and `j ∈ C` and any `x ∈ Γ^k` such that `c(x) = j`,
`|{z ∈ Γ : c(x_i(z)) = κ_i ∀ 1 ≤ i ≤ k}| = γ(κ, j)`", where `x_i(z)` is `x` with its `i`-th entry
replaced by `z`. Stated as "tuples of the same color have the same counts", which is the same
condition. -/
def IsCoherent (c : (Fin k → Fin n) → ℕ) : Prop :=
  ∀ x y, c x = c y → ∀ κ : Fin k → ℕ,
    (Finset.univ.filter fun z : Fin n => ∀ i, c (Function.update x i z) = κ i).card =
      (Finset.univ.filter fun z : Fin n => ∀ i, c (Function.update y i z) = κ i).card

/-- `γ₁, γ₂` are twins for `c` ([H, Section 5.1]: "two elements `γ₁, γ₂ ∈ Γ` are twins with
respect to a structure `X` … if `(γ₁ γ₂) ∈ Aut(X)`"): the transposition preserves every color.
A permutation `σ` acts on tuples by `x ↦ σ ∘ x`. -/
def Twins (c : (Fin k → Fin n) → ℕ) (u v : Fin n) : Prop :=
  ∀ x : Fin k → Fin n, c (Equiv.swap u v ∘ x) = c x

/-- The tuple `(x₁, …, x_ℓ, z, z, …, z)` of length `k`. -/
def padTuple {ℓ : ℕ} (x : Fin ℓ → Fin n) (z : Fin n) : Fin k → Fin n :=
  fun i => if h : i.val < ℓ then x ⟨i.val, h⟩ else z

/-- The tuple `(x₁, …, x_ℓ, z₁, z₂, z₂, …, z₂)` of length `k`. -/
def padTuple₂ {ℓ : ℕ} (x : Fin ℓ → Fin n) (z₁ z₂ : Fin n) : Fin k → Fin n :=
  fun i => if h : i.val < ℓ then x ⟨i.val, h⟩ else if i.val = ℓ then z₁ else z₂

/-- The vertex coloring `X_x^{(1)}` ([H, Definition 2.6 and before Exercise 2.13]): the
individualized structure `c_x(y) = c(x y)` followed by its `1`-skeleton
`c^{(1)}(z) = c(z, z, …, z)`, so `z ↦ c(x₁, …, x_ℓ, z, …, z)`. -/
def skel₁ (c : (Fin k → Fin n) → ℕ) {ℓ : ℕ} (x : Fin ℓ → Fin n) (z : Fin n) : ℕ :=
  c (padTuple x z)

/-- The pair coloring `(X_x)^{(2)}`: `(z₁, z₂) ↦ c(x₁, …, x_ℓ, z₁, z₂, …, z₂)`. -/
def skel₂ (c : (Fin k → Fin n) → ℕ) {ℓ : ℕ} (x : Fin ℓ → Fin n) (z₁ z₂ : Fin n) : ℕ :=
  c (padTuple₂ x z₁ z₂)

/-- **Canonical `k`-ary coherent refinement** ([H, Sections 2.3 and 2.5], the functors `F₁`,
`F₂`, `F₃`; `F₃` is `k`-ary Weisfeiler–Leman, [H, Algorithm 3]). For all `n` and `k` there is a
map `F` on `k`-ary colorings of `Fin n` such that `F c` is a `k`-ary coherent configuration,
the colors of `F c` determine the colors of `c` across inputs (one palette for all inputs), and
`F` commutes with every relabeling of `Fin n`.

*Source, verbatim.* [H, Section 2.3]: "We can define a functor `F₂` sending each `k`-ary
partition structure `X` on `Γ` to a `k`-ary configuration; … `F₂(X)` is a refinement of `X`".
[H, Section 2.5]: "Let us define a functor `F₃` sending a configuration `X = (Γ, c)` to a
coherent configuration `F₃(X) = (Γ, c')`. As `F₃(X)` will be a canonical refinement of `X`, we
will have `Iso(X, Y) = Iso(F₃(X), F₃(Y))`." [H, Section 5]: "We obtain thus a refinement
`F₃(F₂(F₁(X))) = (Γ, c_x : Γ^k → C)` that is a `k`-ary coherent configuration. Since `F₁, F₂, F₃`
are functors, the assignment of `c_x` to `x` is canonical." The paper (Section A.3, before
"Aggregation and orbital colors"): "Use the same palette for both inputs. … Canonical coherent
refinement may then be applied to the resulting full tuple structure."

*Why it is true.* Fix `N = n^k`. One round sends `c` to the coloring whose value at `x` is a
fixed injective code in `ℕ` of: `c(x)`, the equality pattern of `x`, the list
`(c(x ∘ τ))_τ` over all `τ : Fin k → Fin k`, and the finite table of the counts in
`IsCoherent` over the color vectors that occur. Let `F c` be the result of `N` rounds. Each
round is equivariant under `Sym(n)` and its code contains the old color, so `F` is
equivariant and `F c x = F c' y` gives `c x = c' y`. A round that does not change the
partition into color classes changes none later, and a round that does change it adds a class;
there are at most `n^k` classes, so after `N` rounds the partition is stable. Stability means
that equal colors have equal equality patterns, equal colors after every `τ`, and equal counts:
`F c` is a configuration and coherent. The number of rounds does not depend on `c`, so the
codes are comparable between inputs.

*Edge cases.* `n = 0` or `k = 0`: there is at most one tuple and every coloring is a coherent
configuration.

*Why it is the weakest form needed.* The paper needs a coherent configuration that refines the
tuple coloring, uses one palette for both inputs, and is canonical, so that parent isomorphisms
carry one refined structure to the other (`Iso(X, Y) = Iso(F(X), F(Y))` follows from the last
two clauses). Nothing is claimed about its running time here; the algorithm is the task
`GI.Cited.KaryRefinementTask`. -/
def KaryCoherentRefinement : Prop :=
  ∀ n k : ℕ, ∃ F : ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ),
    (∀ c, IsConfiguration (F c) ∧ IsCoherent (F c)) ∧
    (∀ c c' x y, F c x = F c' y → c x = c' y) ∧
    (∀ c (σ : Perm (Fin n)), F (fun x => c (σ.symm ∘ x)) = fun x => F c (σ.symm ∘ x))

end GI.Cited
