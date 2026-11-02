import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Cited input: every point of a transitive group is affected

Source: H. A. Helfgott, J. Bajpai, D. Dona, *Graph isomorphisms in
quasi-polynomial time*, arXiv:1710.04574v1 (12 Oct 2017), Lemma 4.3(a),
cited in the paper as `[H, Lemma 4.3(a)]`. It is a form of Babai's
"unaffected stabilizers" lemma (L. Babai, *Graph isomorphism in
quasipolynomial time*, arXiv:1512.03547v2, Section 8).

Their statement: let `G < Sym(Ω)` and let `φ : G → Alt_k` be an epimorphism
with `k > max(8, 2 + log₂ n₀)`, where `n₀` is the size of the largest orbit
of `G`. If `G` is transitive, every `x ∈ Ω` is affected, that is,
`φ(G_x)` does not contain (here: is not) `Alt_k`.
-/

namespace GI.Cited

open Equiv

/-- **[H, Lemma 4.3(a)]** (Helfgott–Bajpai–Dona, arXiv:1710.04574v1,
Lemma 4.3(a); Babai, arXiv:1512.03547v2, Section 8).

Let `G ≤ Sym(Ω)` be transitive on the finite set `Ω` and let
`φ : G ↠ Alt(k)` be surjective with `k > max(8, 2 + log₂ |Ω|)`.
Then no point stabilizer maps onto `Alt(k)`.

*Why it is true.* Helfgott–Bajpai–Dona derive it from their Lemma 4.1
(a primitive group with an epimorphism onto `Alt(k)` above this threshold is
mapped isomorphically) by passing to a maximal block system and, when the
block kernel maps onto `Alt(k)`, to one orbit of that kernel. Lemma 4.1 uses
O'Nan–Scott, Schreier's conjecture (a consequence of CFSG) for nonabelian
socle, and Babai–Pálfy–Saxl, Prop. 1.22 for abelian socle. The threshold is
sharp: `Alt(8) ≅ GL₄(2)` acting on `F₂⁴` (degree 16) shows `k > 8` is needed,
and `F₂^{k-2} ⋊ Alt(k)` (the heart of the permutation module) shows
`k > 2 + log₂ n` is needed.

*Edge cases.* For `|Ω| ≤ 1` the group is trivial and cannot map onto
`Alt(k)` with `k ≥ 9`, so the statement is vacuous. In Lean,
`Real.logb 2 0 = 0`, which only matters for empty `Ω`, where the conclusion
is vacuous.

*Why this form is minimal.* The paper uses it only for transitive groups
(the proof of Lemma A.15, and through it Corollary A.25), and only the
conclusion "no point stabilizer surjects". For a transitive group the
largest orbit has size `|Ω|`, so `n₀ = |Ω|`. -/
def TransitiveAffected : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Perm Ω))
    [MulAction.IsPretransitive G Ω] (k : ℕ)
    (φ : G →* alternatingGroup (Fin k)),
    Function.Surjective φ →
    max 8 (2 + Real.logb 2 (Fintype.card Ω)) < (k : ℝ) →
    ∀ x : Ω, (MulAction.stabilizer G x).map φ ≠ ⊤

end GI.Cited
