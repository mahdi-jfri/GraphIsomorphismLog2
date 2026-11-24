/-
Main entry point for the stack machine library.

Re-exports the five library theorems needed to simulate log-cost RAM programs on the stack machine:
* `GI.Turing.arithBlocks` (`Workspace.Turing.Lib.ArithDiv`),
* `GI.Turing.lookupBlock` (`Workspace.Turing.Lib.Lookup`),
* `GI.Turing.frontEnd` (`Workspace.Turing.Lib.FrontEnd`),
* `GI.Turing.backEnd` (`Workspace.Turing.Lib.BackEnd`),
* `GI.Turing.simulatesRAM_of` (`Workspace.Turing.Lib.Simulate`).
-/
module

public import Workspace.Turing.Lib.ArithDiv
public import Workspace.Turing.Lib.Lookup
public import Workspace.Turing.Lib.FrontEnd
public import Workspace.Turing.Lib.BackEnd
public import Workspace.Turing.Lib.Simulate

@[expose] public section

namespace GI.Turing

end GI.Turing
