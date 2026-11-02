import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace GI.Cited

/-- **Dixon's bound on the derived length of a solvable permutation group**, in the weaker
form `dl(S) ≤ 5 log₃ n`: for every `n`, every solvable `S ≤ Sym(n)` and every natural number
`k ≥ 5 log₃ n`, the derived subgroup `S^{(k)}` is trivial.

*Source.* J. D. Dixon, *The solvable length of a solvable linear group*, Math. Z. 107 (1968)
151-158. The paper (last paragraph of the proof of Theorem A.20) quotes the sharper
"`dl(S) ≤ (5/2) log₃ b`; see [BA21, Section 12]". Secondary sources differ on the constant:
Arvind, Mukhopadhyay, Nimbhorkar, Vasudev, *Near-optimal expanding generating sets for
solvable permutation groups*, arXiv:1201.3181v1 (2012), Section 3, before Lemma 3.2, write
"By a theorem of Dixon [Dix68], the length k of the derived series of a solvable subgroup
of S_n is bounded by 5 log₃ n". We could not check Dixon's theorem number or constant
directly, so we state the weaker constant `5`, which implies nothing beyond the paper's
claim and is implied by the sharper `5/2`.

*Edge cases.* For `n ≤ 1` the group is trivial, so `S^{(0)} = S = 1`. For `n = 2`, `k ≥ 3.15`,
and `S ≤ C₂` is abelian. For `n = 3, 4`, `k ≥ 5, 7` exceed `dl(S₃) = 2`, `dl(S₄) = 3`. The
iterated wreath products of `S₄` and `S₃`, of degree `4·3^j` and derived length `3 + 2j`,
stay below `(5/2)(log₃ 4 + j)`.

*Why it is the form needed.* The paper needs only `dl(S) = O(log b)` for the solvable
supplement `S ≤ Sym(B)`, to bound the recursion depth in Theorem A.20. The statement uses
the canonical degree-`n` group `Equiv.Perm (Fin n)`.
-/
def DixonDerivedLength : Prop :=
  ∀ (n : ℕ) (S : Subgroup (Equiv.Perm (Fin n))), IsSolvable S →
    ∀ k : ℕ, 5 * Real.logb 3 n ≤ k → derivedSeries S k = ⊥

end GI.Cited
