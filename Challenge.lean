module

public import Workspace.Statement.Main

/-!
# Graph isomorphism in quasipolynomial time: the statement to be proved

`GI.graphIsomorphismInQuasipolynomialTime` is Theorem 1.1 of the paper: graph isomorphism is
decidable in quasipolynomial time. The statement is `GI.Statement.GraphIsomorphismInQuasipolynomialTime`,
defined in `Workspace/Statement/Main.lean` and `Workspace/Statement/Machine.lean`.
`Solution.lean` proves it.
-/

public section

theorem GI.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  sorry
