/-
The main theorem for Turing machines, from the main theorem for the log-cost machine.

`GI.Turing.turingGraphIsomorphismInDegreeTime_of` turns a program for the machine of
`Workspace.Statement.Machine` with the bound of `GI.Statement.GraphIsomorphismInDegreeTime` into a
Turing machine with the bound of `GI.Statement.TuringGraphIsomorphismInDegreeTime`. It puts
together the parts stated in `Workspace.Turing.Interface`:

* the wrapper program, which reads and writes bits (`GI.Turing.turing_of`);
* the log-cost machine on the stack machine (`GI.Turing.simulatesRAM_of`, built from
  `GI.Turing.coreSim_of` and the blocks of `Workspace.Turing.Lib`);
* the stack machine on a Turing machine (`GI.Turing.simulatesSM`).
-/
module

public import Workspace.Turing.Wrap.Main
public import Workspace.Turing.Lib.Main
public import Workspace.Turing.Core.Main
public import Workspace.Turing.TM.Main

@[expose] public section

namespace GI.Turing

/-- Every program of the log-cost machine runs on the stack machine with a polynomial
slowdown. -/
theorem simulatesRAM : SimulatesRAM :=
  simulatesRAM_of frontEnd backEnd (coreSim_of arithBlocks lookupBlock)

/-- **Theorem 1.1 for Turing machines**, from Theorem 1.1 for the log-cost machine. -/
theorem turingGraphIsomorphismInDegreeTime_of
    (h : GI.Statement.GraphIsomorphismInDegreeTime) :
    GI.Statement.TuringGraphIsomorphismInDegreeTime :=
  turing_of h simulatesRAM simulatesSM

/-- **Corollary 1.2 for Turing machines**, from Theorem 1.1 for the log-cost machine. -/
theorem turingGraphIsomorphismInQuasipolynomialTime_of
    (h : GI.Statement.GraphIsomorphismInDegreeTime) :
    GI.Statement.TuringGraphIsomorphismInQuasipolynomialTime :=
  GI.Statement.turingQuasipolynomialTime_of_degreeTime (turingGraphIsomorphismInDegreeTime_of h)

end GI.Turing
