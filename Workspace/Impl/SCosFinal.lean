import Workspace.Impl.SCosSolve2
import Workspace.Impl.SCosBig

/-!
# Solvable coset intersection, as a reduction

`scos_solvableCosetIntersection`: from the Pálfy–Wolf bound and the cited tasks pointwise
stabilizer, preimage and minimal blocks, the program `scosProgram` ([LM, Proposition 3.9])
solves `SolvableCosetIntersectionTask` in polynomial time. The exponent `c` of the program is
the one of `scos_palfy_classes`; the transitive step is `scos_big_spec`, and the rest is
`scos_reduction_of_big`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-- **Solvable coset intersection** ([LM, Proposition 3.9]). -/
theorem scos_solvableCosetIntersection (hP : ScosPalfyBound) (hps : PointwiseStab)
    (hpre : Preimage) (hmb : MinimalBlocks) : SolvableCosetIntersection := by
  obtain ⟨c, hc⟩ := scos_palfyC hP
  exact scos_reduction_of_big (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)
    (fun n => scosOwnG hps hpre hmb n c) (scosBigK hps hpre hmb c) (scosBigE hps hpre hmb c)
    (fun n => scosOwnG_le hps hpre hmb n c)
    (fun _ _ _ _ _ hv ht h2 T hrec => scos_big_spec hc hv ht h2 T hrec)

end GI.Impl
