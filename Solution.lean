module

public import Workspace.Assembly.Main

/-!
# Graph isomorphism in quasipolynomial time

This file proves the statement of `Challenge.lean`: Theorem 1.1 of the paper, in the
model of `Workspace/Statement/Main.lean`. The proof is
`GI.Assembly.graphIsomorphismInQuasipolynomialTime` (`Workspace/Assembly/Main.lean`).
-/

public section

/-- **Theorem 1.1.** Graph isomorphism is decidable in quasipolynomial time, in the model of
`Workspace/Statement/Main.lean`. -/
theorem GI.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  GI.Assembly.graphIsomorphismInQuasipolynomialTime

#print axioms GI.graphIsomorphismInQuasipolynomialTime
