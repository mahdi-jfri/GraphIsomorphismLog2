import Workspace.Assembly.Main

/-!
# The solution

The statement of `Challenge.lean`, proved by `GI.graphIsomorphismInQuasipolynomialTime`
(`Workspace/Assembly/Main.lean`).
-/

theorem main_theorem : GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  GI.graphIsomorphismInQuasipolynomialTime
