module

public import Workspace.Degree.MainDeg
public import Workspace.Degree.GraphFinal
public import Workspace.Turing.Main

/-!
# Graph isomorphism in time `n ^ O(log d)` on Turing machines: the proof

This file proves the two theorems of `Challenge.lean`, for Mathlib's Turing
machines. The proof has two steps.

* `GI.Degree.graphIsomorphismInDegreeTime_of` (`Workspace/Degree/MainDeg.lean`), applied to the
  graph theorem `GI.Degree.graphSolver` (`Workspace/Degree/GraphFinal.lean`), gives a program of
  the log-cost machine of `Workspace/Statement/Machine.lean` with the bound of Theorem 1.1.
* `GI.Turing.turingGraphIsomorphismInDegreeTime_of` (`Workspace/Turing/Main.lean`) runs that
  program on a Turing machine with a polynomial slowdown. A polynomial of
  `exp (C * log (n + 2) * log (d + 2))` is again of that form.
-/

public section

/-- **Theorem 1.1 of the paper, for Turing machines**: graph isomorphism for graphs of degree at
most `d` in `exp (C * log (n + 2) * log (d + 2))` steps of a Mathlib Turing machine. -/
theorem GI.turingGraphIsomorphismInDegreeTime : GI.Statement.TuringGraphIsomorphismInDegreeTime :=
  GI.Turing.turingGraphIsomorphismInDegreeTime_of
    (GI.Degree.graphIsomorphismInDegreeTime_of GI.Degree.graphSolver)

/-- **Corollary 1.2 of the paper, for Turing machines**: graph isomorphism in
`exp (C * (log (n + 2)) ^ 2)` steps of a Mathlib Turing machine. -/
theorem GI.turingGraphIsomorphismInQuasipolynomialTime :
    GI.Statement.TuringGraphIsomorphismInQuasipolynomialTime :=
  GI.Statement.turingQuasipolynomialTime_of_degreeTime GI.turingGraphIsomorphismInDegreeTime

#print axioms GI.turingGraphIsomorphismInDegreeTime
#print axioms GI.turingGraphIsomorphismInQuasipolynomialTime
