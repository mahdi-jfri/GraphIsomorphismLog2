module

public import Workspace.Assembly.Main

/-!
# Graph isomorphism in quasipolynomial time

This file proves the statement of `Challenge.lean`: Corollary 1.2 of the paper, in the
model of `Workspace/Statement/Main.lean`. The proof is
`GI.Assembly.graphIsomorphismInQuasipolynomialTime` (`Workspace/Assembly/Main.lean`).
-/

public section

/-- **Corollary 1.2.** Graph isomorphism is decidable in quasipolynomial time, in the model of
`Workspace/Statement/Main.lean`. -/
theorem GI.graphIsomorphismInQuasipolynomialTime :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  GI.Assembly.graphIsomorphismInQuasipolynomialTime

#print axioms GI.graphIsomorphismInQuasipolynomialTime
