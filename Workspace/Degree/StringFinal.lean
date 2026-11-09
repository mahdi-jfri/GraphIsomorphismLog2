module

public import Workspace.Degree.LayoutThread
public import Workspace.Degree.Recog

@[expose] public section

/-!
# The string theorem with no hypotheses

`stringSolver` of `Degree/LayoutThread.lean` takes the recognition `JohnsonRecognition` as its
one hypothesis. `johnsonRecognition` (`Degree/Recog.lean`) proves it, so the string theorem holds
for the program `strProgFinal` with no hypotheses.
-/

namespace GI.Degree

/-- The program of the string theorem, with the recognition of `Degree/Recog.lean`. -/
noncomputable def strProgFinal : GI.Lang.Program := strProg johnsonRecognition

/-- **The string theorem**, with no hypotheses. -/
theorem stringSolver_final : StringSolver strProgFinal (dgb 40) := stringSolver johnsonRecognition

end GI.Degree
