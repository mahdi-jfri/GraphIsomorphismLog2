module

public import Workspace.Degree.MainDeg
public import Workspace.Degree.GraphFinal

/-!
# Graph isomorphism in time `n ^ O(log d)`

This file proves the statement of `ChallengeDegree.lean`: Theorem 1.1 of the
paper, in the model of `Workspace/Statement/Degree.lean`. The proof is `GI.Degree.graphIsomorphismInDegreeTime_of` (`Workspace/Degree/MainDeg.lean`), applied to
the graph theorem `GI.Degree.graphSolver : GI.Degree.GraphSolver GI.Degree.graphFuns`
(`Workspace/Degree/GraphFinal.lean`).
-/

public section

/-- **Theorem 1.1 of the paper**: graph isomorphism for graphs of degree at most `d` in time
`exp(C log(n + 2) log(d + 2))`. -/
theorem GI.graphIsomorphismInDegreeTime : GI.Statement.GraphIsomorphismInDegreeTime :=
  GI.Degree.graphIsomorphismInDegreeTime_of GI.Degree.graphSolver

#print axioms GI.graphIsomorphismInDegreeTime
