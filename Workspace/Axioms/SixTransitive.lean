/-
Axiom: A 6-transitive group of degree `n ≥ 6` contains `Alt(n)`, a consequence of CFSG. The paper uses it in the aggregation step ([H, Section 6.2], Case 2b, "By CFSG, d ≤ 5"). The statement and the reasons it is true are in `GI.Cited.SixTransitiveContainsAlt`.
-/
import Workspace.Cited.SixTransitive

namespace GI.Axioms

/-- A 6-transitive subgroup of `Sym(n)`, `n ≥ 6`, contains `Alt(n)`. -/
axiom sixTransitiveContainsAlt : GI.Cited.SixTransitiveContainsAlt

end GI.Axioms
