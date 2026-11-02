/-
Axioms: the cited permutation-group algorithm tasks used by `GI.Assembly.final_modulo_contracts`.
Each axiom's type is the task `∃ p, PolyTimeAt T p` of `Workspace/Cited/AlgoPermGroups.lean`, used
as is. `AXIOMS.md` discusses each one.
Sources: [L93] = Luks, *Permutation groups and polynomial-time computation*, DIMACS 11 (1993);
[LM] = Luks, Miyazaki, *Polynomial-time normalizers*, DMTCS 13:4 (2011); [H] = Helfgott, Bajpai,
Dona, arXiv:1710.04574v1.
-/
import Workspace.Cited.AlgoPermGroups

namespace GI.Axioms

/-- A chief series in polynomial time: [LM, Theorem 3.1(x), p. 68]; Seress, *Permutation Group
Algorithms* (2003), §6.2.7. -/
axiom chiefSeriesAlgo : GI.Cited.ChiefSeriesAlgo

/-- Centralizer in a quotient, in polynomial time: [LM, Lemma 3.2, p. 68] (Kantor–Luks; uses
CFSG). Kept in its published form. -/
axiom quotientCentralizer : GI.Cited.QuotientCentralizer

/-- A Sylow subgroup in polynomial time: [LM, Theorem 3.1(xi)]; [L93, Lemma 8.3(i), p. 163]
(Kantor 1985; uses CFSG). -/
axiom sylowAlgo : GI.Cited.SylowAlgo

/-- Conjugating one Sylow subgroup to another, in polynomial time: [LM, Theorem 3.1(xi)];
[L93, Lemma 8.3(ii), p. 163]. -/
axiom sylowConjugate : GI.Cited.SylowConjugate

end GI.Axioms
