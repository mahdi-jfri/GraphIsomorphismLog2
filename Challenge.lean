import Workspace.Statement.Main
import Workspace.Axioms.AlgoPermGroups
import Workspace.Axioms.GMP
import Workspace.Axioms.MarotiPrimitive
import Workspace.Axioms.SimpleValuationDegree
import Workspace.Axioms.SixTransitive
import Workspace.Axioms.TransitiveAffected

/-!
# The challenge

The main theorem of the paper, stated with `sorry`. Comparator checks that `Solution.lean`
proves this exact statement (see `comparator.json` and the README).

The statement and its machine model are defined in `Workspace/Statement/Main.lean` and
`Workspace/Statement/Machine.lean`. These two files are all a reader must check to know what is
claimed.

The challenge also imports the ten axioms of `Workspace/Axioms/`. Comparator allows them in the
solution only with the same statements as here. Their statements are definitions in
`Workspace/Cited/` (see `AXIOMS.md`).
-/

/-- **Theorem 1.1.** There are one program `p` and one constant `C` such that, for every `n` and
all graphs `G` and `H` on `n` vertices, the run of `p` on the adjacency matrices of `G` and `H`
finishes with a correct output, at a cost of at most `exp (C * (log (n + 2)) ^ 2)`. A correct
output says whether `G` and `H` are isomorphic. If they are, it also gives one isomorphism and
generators of the automorphism group of `G`. -/
theorem main_theorem : GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  sorry
