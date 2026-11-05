module

public import Workspace.Cited.CoherentConfig
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Cited input: Babai's Design Lemma ([H, Proposition 5.1])
-/

namespace GI.Cited

/-- **The Design Lemma** ([H, Proposition 5.1], Babai), for a dominance threshold
`1/2 < α < 1` and a strict twin hypothesis. Let `c` be a `k`-ary coherent configuration on
`Fin n`, `2 ≤ k ≤ n/2`, in which every set of pairwise twins has fewer than `α n` points. Then
(a) for some `ℓ < k` and some `x ∈ Γ^ℓ`, every color class of the vertex coloring
`z ↦ c(x, z, …, z)` has fewer than `α n` points; or (b) for some `ℓ < k - 1` and some
`x ∈ Γ^ℓ`, some color class `C` of that vertex coloring has at least `α n` points and the pair
coloring `(z₁, z₂) ↦ c(x, z₁, z₂, …, z₂)` is not constant on the pairs of distinct points of `C`.

*Source.* [H] = Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*,
arXiv:1710.04574v1 (12 Oct 2017), Section 5.1. Verbatim: "a color `i` is called `α`-dominant if
`c(γ, …, γ) = i` for `≥ α|Γ|` values of `γ ∈ Γ`." "Proposition 5.1 (Design Lemma). — Let
`X = (Γ, c : Γ^k → C)` a `k`-ary coherent configuration, where `2 ≤ k ≤ |Γ|/2`. Let
`1/2 ≤ α < 1`. Suppose that there is no twin class in `Γ` with `> α|Γ|` elements. Then, at least
one of the following options is true: (a) there exist `x₁, …, x_ℓ ∈ Γ`, `0 ≤ ℓ < k`, such that
`X_x^{(1)}` has no `α`-dominant color; (b) there exist `x₁, …, x_ℓ ∈ Γ`, `0 ≤ ℓ < k − 1`, such
that `X_x^{(1)}` has an `α`-dominant color `C` and `(X_x)^{(2)}[C]` is not a clique."

*Why we do not state [H]'s form.* As written, with `α = 1/2`, it is false. Take `n = 4`, `k = 2`,
`Γ = A ⊔ B` with `|A| = |B| = 2`, and `c` the orbital coloring of `Sym(A) × Sym(B)` (colors:
the diagonal of `A`, the diagonal of `B`, and the off-diagonal pairs inside `A`, inside `B`,
from `A` to `B`, from `B` to `A`). It is a coherent configuration (it is Schurian). The twin
classes are `A` and `B`, of size `2 = α n`, so the hypothesis holds. For `ℓ = 0` both vertex
classes have size `2 ≥ α n`; for `ℓ = 1` and `x = a ∈ A` the classes of `z ↦ c(a, z)` are `{a}`,
`A \ {a}` and `B`, and `B` has size `2`; so (a) fails. Option (b) needs `ℓ = 0`, and on `A` and
on `B` the pair coloring is a clique; so (b) fails. [H]'s proof uses strict inequalities at two
places ("Since `|C| > α|Γ|`, `C` is too big to be a twin set", and "Since
`|C(x)|, |C(y)| > α|Γ| ≥ |Γ|/2`, the two last possibilities are excluded"), which hold when
`α > 1/2` and no twin class has `≥ α n` points.

*Why this form is true.* [H]'s proof goes through verbatim under our hypotheses. Suppose every
`X_x^{(1)}`, `ℓ < k`, has a class `C(x)` of size `≥ α n`; it is unique since `α > 1/2`. Suppose
also that for `ℓ < k - 1` the pair coloring on `C(x)` is a clique. By the large clique lemma
([H, Lemma 5.2], from Fisher's inequality; it needs `|C| > n/2`, which holds), `C(y)` is a twin
class of `(X_y)^{(2)}`, which gives `C(yz) = C(y) \ {z}` (two classes of size `> n/2` cannot be
disjoint). The class `C = C(∅)` has `≥ α n` points, so it is not a set of pairwise twins of
`X`: some `u, v ∈ C` have `(u v) ∉ Aut(X)`. A shortest tuple whose color changes under `(u v)`
gives, after reordering by axiom (b) of configurations, either `c_x(u) ≠ c_x(v)` with
`ℓ = r - 1 < k`, or `c_x(u, v) ≠ c_x(v, u)` with `ℓ = r - 2 < k - 1`, and `u, v ∈ C(x)`; both
contradict the assumptions.

*Edge cases.* `k ≥ 2` and `2k ≤ n` are [H]'s hypotheses. The twin hypothesis is about every set
of pairwise twins (twinness is an equivalence relation, so these are the subsets of twin
classes). In (b), "not a clique" is stated as two pairs of distinct points of `C` with
different colors; the diagonal of `C` has one color, since `C` is a vertex color class.

*Why it is the weakest form needed.* The paper applies the Design Lemma to the canonical
coherent refinement of the comparison-class coloring of `k`-tuples (Section A.3, Case 3 of the
aggregation), where no twin class has `κ` or more points and `κ` is a constant much smaller
than the number of labels; it uses that "the Design Lemma's dominant class contains more than
half the remaining labels" (Section A.3, "Balance parameters"). Any fixed `α ∈ (1/2, 1)` serves:
outcome (a) is the balanced coloring, outcome (b) the nontrivial homogeneous coherent
configuration on `C`, `|C| ≥ α n`. -/
def DesignLemma : Prop :=
  ∀ (n k : ℕ), 2 ≤ k → 2 * k ≤ n → ∀ α : ℝ, 1 / 2 < α → α < 1 →
    ∀ c : (Fin k → Fin n) → ℕ, IsConfiguration c → IsCoherent c →
    (∀ S : Finset (Fin n), (∀ u ∈ S, ∀ v ∈ S, Twins c u v) → (S.card : ℝ) < α * n) →
    (∃ ℓ < k, ∃ x : Fin ℓ → Fin n, ∀ j : ℕ,
        ((Finset.univ.filter fun z => skel₁ c x z = j).card : ℝ) < α * n) ∨
    (∃ ℓ, ℓ + 1 < k ∧ ∃ x : Fin ℓ → Fin n, ∃ j : ℕ,
        α * n ≤ ((Finset.univ.filter fun z => skel₁ c x z = j).card : ℝ) ∧
        ∃ u v w y : Fin n, skel₁ c x u = j ∧ skel₁ c x v = j ∧ skel₁ c x w = j ∧
          skel₁ c x y = j ∧ u ≠ v ∧ w ≠ y ∧ skel₂ c x u v ≠ skel₂ c x w y)

end GI.Cited
