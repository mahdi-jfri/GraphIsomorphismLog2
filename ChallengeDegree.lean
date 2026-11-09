module

public import Workspace.Statement.Degree

/-!
# Graph isomorphism in time `n ^ O(log d)`: the statement to be proved

`GI.graphIsomorphismInDegreeTime` is Theorem 1.1 of the paper: graph isomorphism
for graphs of maximum degree `d` is decidable in time `n ^ O(log d)`.
The statement is `GI.Statement.GraphIsomorphismInDegreeTime`, defined in
`Workspace/Statement/Degree.lean`.
-/

public section

theorem GI.graphIsomorphismInDegreeTime : GI.Statement.GraphIsomorphismInDegreeTime :=
  sorry
