import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Cited input: a 6-transitive group contains the alternating group (CFSG)
-/

namespace GI.Cited

open Equiv

/-- **Six-transitive groups are giants** (a consequence of the classification of finite simple
groups). For every `n ≥ 6` and every `G ≤ Sym(n)` that is transitive on ordered 6-tuples of
distinct points, `Alt(n) ≤ G`.

*Source.* [H] = Helfgott, Bajpai, Dona, *Graph isomorphisms in quasi-polynomial time*,
arXiv:1710.04574v1 (12 Oct 2017), Section 6.2, Case 2b, verbatim: "Let `d ≥ 1` be the maximal
integer with the property that `φ(F)|_Φ` is `d`-transitive, i.e., `φ(F)|_Φ` acts transitively on
the set of `d`-tuples of distinct elements of `Φ`. By CFSG, `d ≤ 5`; if we do not want to use
CFSG, we have the classical bound `d ≪ log |Γ|`." Here `Alt(Φ) ≮ φ(F)|_Φ`. The paper
(Section A.3, "Aggregation and orbital colors"): "let `d ≤ 5` be its maximal degree of
transitivity, using the CFSG bound stated there."

*Why it is true.* By CFSG, the 4-transitive finite permutation groups are `Sym(n)` (`n ≥ 4`),
`Alt(n)` (`n ≥ 6`) and the Mathieu groups `M_11, M_12, M_23, M_24` in their natural actions;
`M_11` and `M_23` are exactly 4-transitive and `M_12`, `M_24` exactly 5-transitive. So a
6-transitive group of degree `n ≥ 6` is `Sym(n)` or `Alt(n)`. We did not locate a theorem number
for this list in a primary source; [H] states the consequence `d ≤ 5` directly. The small degrees
need no classification: on `6` or `7` points a 6-transitive group has order at least `6!` or
`7!`, so it is the whole symmetric group, and on `8` points its order is at least `8!/2`, so it
contains `Alt(8)`.

*Edge cases.* `n ≥ 6` is required: for `n < 6` there are no injective 6-tuples, so every group
is vacuously 6-transitive, while `Alt(4)` and `Alt(5)` are not trivial.

*Why it is the weakest form needed.* The paper needs only `d ≤ 5` for a group on the dominant
orbit `Φ` (`|Φ| > q/2 ≥ 6`) whose image does not contain `Alt(Φ)`. That is the contrapositive
of this statement for `n = |Φ|`. It bounds the anchor branches by `q^{d-1} ≤ q^4`. It is stated
for subgroups of `Perm (Fin n)`, with 6-transitivity written out with embeddings
`Fin 6 ↪ Fin n`. -/
def SixTransitiveContainsAlt : Prop :=
  ∀ (n : ℕ), 6 ≤ n → ∀ (G : Subgroup (Perm (Fin n))),
    (∀ a b : Fin 6 ↪ Fin n, ∃ g ∈ G, ∀ i, g (a i) = b i) →
    alternatingGroup (Fin n) ≤ G

end GI.Cited
