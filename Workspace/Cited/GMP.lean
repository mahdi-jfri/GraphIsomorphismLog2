import Workspace.Cited.CompositionFactors
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.End
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Three results of Guralnick, Maróti and Pyber

[GMP] = R. M. Guralnick, A. Maróti, L. Pyber, *Normalizers of primitive permutation groups*,
Adv. Math. 310 (2017) 1017-1063. We read arXiv:1603.00187v2 (27 January 2017). In [GMP] the
base of logarithms is 2 ("Throughout the paper the base of the logarithms is 2 unless otherwise
stated", p. 2). The products `a(X)`, `b(X)` are those of `GI.Cited.CompositionProducts`.

The paper uses all three in the proof of Lemma A.21 (`lem:radical-free-order`) and of
Corollary A.22 (`cor:transitive-kernel-multicoset`).
-/

namespace GI.Cited

/-- **[GMP, Proposition 6.1], abelian part.** For every subgroup `P ≤ Sym(n)` with `n ≥ 1`,
`a(P) ≤ 24^{(n-1)/3}`.

*Source, verbatim (arXiv v2, Section 6).* "Proposition 6.1. Let `G ≤ S_n`. The product of the
orders of all composition factors of `G` which are not isomorphic to alternating groups of
degrees larger than `d ≥ 4` is at most `d!^{(n-1)/(d-1)}`. In particular, `a_2(G)` and `a_3(G)`
are at most `24^{(n-1)/3}` ..." Here `a_p(G)` is the product of the orders of the composition
factors that are `p`-groups or `p'`-groups, and the text before the proposition says "Clearly
`a(G) ≤ a_p(G)` for any prime `p`" (an abelian composition factor has prime order, so it is a
`p`-group or a `p'`-group), and "By a theorem of Dixon [D] this implies ... that `a(G)` is at
most `24^{(n-1)/3}` for any subgroup `G` of `S_n`." The paper cites exactly this:
"By [GMP, Proposition 6.1], `a(P) ≤ 24^{(t-1)/3}`."

*Why it is true.* `a(G)` is at most the order of a solvable subgroup of `G` ([GMP, Section 6]),
and Dixon's theorem bounds a solvable subgroup of `S_n` by `24^{(n-1)/3}`.

*Edge cases.* `n ≥ 1` is required: for `n = 0` the right side is `24^{-1/3} < 1 = a(1)`. For
`n = 1` both sides are `1`. For `n = 4`, `a(S_4) = 24 = 24^{3/3}`, so the bound is sharp.

*Form.* Stated for every composition series (Jordan-Hölder makes `a` independent of it), for
subgroups of the canonical `Equiv.Perm (Fin n)`. -/
def GMPAbelianFactors : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (P : Subgroup (Equiv.Perm (Fin n))) (a b : ℕ),
    CompositionProducts P a b → (a : ℝ) ≤ (24 : ℝ) ^ (((n : ℝ) - 1) / 3)

/-- **[GMP, Lemma 7.7], applied to the regular representation.** For every finite nonabelian
simple group `T`, `|Out(T)| ≤ 2 √|T|`. Here `|Out(T)|` is the index of the inner automorphisms
`MulAut.conj.range` in `MulAut T`.

*Source, verbatim (arXiv v2, Section 7).* "Lemma 7.7. Let `S` be a nonabelian finite simple
group and suppose that `S` has a nontrivial permutation representation of degree `n`. Then
`|Out(S)| ≤ 2 log n` or `S = L_d(q)` with `d > 2` or `S = PΩ⁺₈(3^e)` with `e` an integer, and
`|Out(S)| ≤ 3 log n`. In all cases we have `|Out(S)| ≤ 2 √n`. ..." The regular representation
of `T` is a nontrivial permutation representation of degree `|T|`, so `|Out(T)| ≤ 2 √|T|`.
The paper: "By [GMP, Lemma 7.7], applied to the regular representation of `T_i`,
`|Out(T_i)| ≤ 2 √|T_i|`."

*Why it is true.* By the classification, `|Out(T)| ≤ 4` for alternating and sporadic `T`, and
for `T` of Lie type over `𝔽_q`, `q = p^f`, of rank `r`, `|Out(T)|` is at most a small multiple
of `(r+1) f`, while `|T| ≥ q^r`. The extreme small cases: `A_5` (`|Out| = 2`, `2√60 ≈ 15.5`),
`A_6` (`4`, `2√360 ≈ 37.9`), `PSL_3(4)` (`12`, `2√20160 ≈ 284`).

*Form.* The weakest form the paper uses: only the regular representation. Stated for groups in
`Type`; the proof of Lemma A.21 transfers it along isomorphisms. -/
def GMPOutBound : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ x y : T, x * y ≠ y * x) →
    ((MulAut.conj : T →* MulAut T).range.index : ℝ) ≤ 2 * Real.sqrt (Nat.card T)

/-- **[GMP, Theorem 1.4], transitive case.** If `G ◁ A ≤ Sym(n)`, `n ≥ 1`, and `G` is
transitive, then `b(A/G) ≤ n^{log₂ n}`.

*Source, verbatim (arXiv v2, Section 1).* "Theorem 1.4. Let `A` and `G` be permutation groups
with `G ⊳ A ≤ S_n`. If `G` is transitive, then `b(A/G) ≤ n^{log n}`. If `G` is primitive, then
`b(A/G) ≤ (log n)^{2 log log n}`." Logarithms are to base 2. The paper: "Theorem 1.4 of [GMP]
and Lemma A.21 give `[H:R] ≤ b(Q)^2 ≤ b^{2 log₂ b}`" for `N ◁ H ≤ Sym(B)`, `N` transitive,
`Q = H/N`.

*Why it is true.* [GMP, Theorem 5.1] proves the strict bound `b(A/G) < n^{log n}` for
nontrivial transitive `G ◁ A` by induction on a block system, through the O'Nan-Scott
theorem and Schreier's conjecture (CFSG). When `G` is trivial and transitive, `n = 1` and
`b = 1 = 1^0`.

*Edge cases.* `n ≥ 1` (a transitive group acts on a nonempty set). For `n = 1, 2` the
bounds are `1` and `2`, and `A/G` is trivial or of order `2`, so `b(A/G) = 1`.

*Form.* For every composition series of `A/G`, for subgroups of `Equiv.Perm (Fin n)`. `G ◁ A`
is `G ≤ A` together with normality of `G` inside `A`. -/
def GMPTransitiveNonabelian : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (A G : Subgroup (Equiv.Perm (Fin n))), G ≤ A →
    ∀ [(G.subgroupOf A).Normal], MulAction.IsPretransitive G (Fin n) →
    ∀ a b : ℕ, CompositionProducts (A ⧸ G.subgroupOf A) a b →
      (b : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n

end GI.Cited
