/-
Axiom: [H, Lemma 4.3(a)] (Helfgott, Bajpai, Dona, arXiv:1710.04574v1; Babai, arXiv:1512.03547v2,
Section 8). Its statement and the reasons it is true are in `GI.Cited.TransitiveAffected`. The paper
cites it in the proof of Lemma A.15 and does not prove it; it rests on CFSG through Schreier's
conjecture.
-/
import Workspace.Cited.TransitiveAffected

namespace GI.Axioms

/-- [H, Lemma 4.3(a)]: in a transitive group with an epimorphism onto `Alt(k)`,
`k > max(8, 2 + log₂ n)`, no point stabilizer maps onto `Alt(k)`. -/
axiom transitiveAffected : GI.Cited.TransitiveAffected

end GI.Axioms
