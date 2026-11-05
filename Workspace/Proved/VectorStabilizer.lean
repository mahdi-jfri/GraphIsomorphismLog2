module

public import Workspace.Impl.VsHProg

@[expose] public section

/-!
# Vector stabilizers in polynomial time

`GI.Proved.vectorStabilizer` proves `GI.Cited.VectorStabilizer` (Luks and Miyazaki, DMTCS 13:4
(2011), Theorem 1.4(i), p. 64) by the program `vsQProgP` with the extra blocks `vsHBlocks` of the
hard case and the `Q₈` continuation (`GI.Impl.vsQ_vectorStabilizer_of`, `GI.Impl.vsH_HQ`).
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl

/-- **The vector stabilizer** ([LM, Theorem 1.4(i)]), proved. -/
theorem vectorStabilizer : GI.Cited.VectorStabilizer := by
  have L := vsHLay GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.minimalBlocks
    GI.Proved.normalClosure GI.Proved.derivedSubgroup GI.Proved.constructiveMembership
  refine vsQ_vectorStabilizer_of vsHIdx.h.hard vsHIdx.q8c vsHBlocks
    (vsHHardCH GI.Proved.pointwiseStab GI.Proved.membership)
    (vsHCQ GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.normalClosure GI.Proved.derivedSubgroup)
    ?_ ?_ (vsH_HQ L)
  · obtain ⟨K, D, h⟩ := vsHHardCH_bound GI.Proved.pointwiseStab GI.Proved.membership
    exact ⟨K, D, fun Cφ I S hS => h I S Cφ (by omega)⟩
  · obtain ⟨K, D, h⟩ := vsHCQ_bound GI.Proved.pointwiseStab GI.Proved.membership GI.Proved.normalClosure
      GI.Proved.derivedSubgroup
    exact ⟨K, D, fun Cφ I S hS => h I S Cφ (by omega)⟩

end GI.Proved
