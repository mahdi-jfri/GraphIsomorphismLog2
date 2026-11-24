/-
Checks of the Turing machine statement (`Workspace.Statement.Turing`).

This module imports:
* `Workspace.Turing.Checks.Encoding`: prefix-freeness and injectivity of `natBits`, `mapBits`,
  `answerBits`, `adjBits` and `inputBits`, plus the length separation of inputs of different sizes.
* `Workspace.Turing.Checks.Answer`: existence of a correct answer for every pair of graphs.
-/
module

public import Workspace.Turing.Checks.Encoding
public import Workspace.Turing.Checks.Answer
