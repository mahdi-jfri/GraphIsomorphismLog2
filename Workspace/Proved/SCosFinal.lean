import Workspace.Impl.SCosFinal
import Workspace.Proved.Palfy
import Workspace.Proved.SSPointwiseStab
import Workspace.Proved.NClPreimage
import Workspace.Proved.MBlk

/-!
# Solvable coset intersection, proved

[LM] = Luks–Miyazaki, DMTCS 13:4 (2011), Proposition 3.9: the divide-and-conquer program
`GI.Impl.scosProgram` (`Workspace/Impl/SCos*.lean`), with the Pálfy–Wolf bound
(`GI.Proved.palfyBound`) and the proved tasks pointwise stabilizer, preimage and minimal blocks.
-/

namespace GI.Proved

/-- `ScosPalfyBound` is `PalfyBound`, word for word. -/
theorem scosPalfyBound : ScosPalfyBound := palfyBound

/-- **Coset intersection with a solvable group** ([LM, Proposition 3.9]). -/
theorem solvableCosetIntersection : GI.Cited.SolvableCosetIntersection :=
  GI.Impl.scos_solvableCosetIntersection scosPalfyBound pointwiseStab preimage minimalBlocks

end GI.Proved
