/-
Axioms from Guralnick, Maróti, Pyber, "Normalizers of primitive permutation groups", Adv. Math. 310
(2017) 1017-1063 (arXiv:1603.00187v2): Lemma 7.7 and Theorem 1.4. The paper uses them in Lemmas A.8
and A.21 and Corollary A.22. Lemma 7.7 rests on CFSG. The statements and the
reasons they are true are in `Workspace/Cited/GMP.lean`. The bound `|Aut T| ≤ |T|²` used in
Lemma A.8 follows from Lemma 7.7 (`GI.autCardLeSq_of_outBound`).
-/
import Workspace.Cited.GMP

namespace GI.Axioms

/-- [GMP, Lemma 7.7], for the regular representation: `|Out T| ≤ 2 √|T|` for a finite nonabelian
simple group `T`. -/
axiom gmpOutBound : GI.Cited.GMPOutBound

/-- [GMP, Theorem 1.4], transitive case: if `G ◁ A ≤ Sym(n)` and `G` is transitive, the
nonabelian composition factors of `A/G` have product at most `n^{log₂ n}`. -/
axiom gmpTransitiveNonabelian : GI.Cited.GMPTransitiveNonabelian

end GI.Axioms
