/-
Axiom: Maróti's theorem on the orders of primitive groups (J. Algebra 258 (2002), Theorem 1.1), for degree at least 25. The paper cites it through [H, Theorem 3.1] in the dispatcher and in Corollary A.13. It rests on CFSG. The statement and the reasons it is true are in `GI.Cited.MarotiPrimitive`.
-/
import Workspace.Cited.MarotiPrimitive

namespace GI.Axioms

/-- A primitive group of degree `n ≥ 25` has order below `n^{1+⌊log₂ n⌋}` or lies in `Sym(m) wr Sym(r)` in product action on `k`-sets and contains `Alt(m)^r`. -/
axiom marotiPrimitive : GI.Cited.MarotiPrimitive

end GI.Axioms
