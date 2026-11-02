/-
Axiom: for a finite nonabelian simple group `T` not isomorphic to an alternating group, some
`ℓ ∈ {3, 5}` has `v_ℓ(|Aut(T)|) = O(log n)` for every faithful action of `T` on `n` points. The paper
derives this in the proof of Lemma A.8 from CFSG, the order formulas for groups of Lie type, their
outer automorphism groups, and the minimal degrees in [GMPS, Table 4]. The statement and the reasons
it is true are in `GI.Cited.SimpleValuationDegree`.
-/
import Workspace.Cited.SimpleValuationDegree

namespace GI.Axioms

/-- The valuation of `|Aut(T)|` at 3 or 5 is logarithmic in the degree of any faithful action of a
nonalternating finite simple group `T`. -/
axiom simpleValuationDegree : GI.Cited.SimpleValuationDegree

end GI.Axioms
