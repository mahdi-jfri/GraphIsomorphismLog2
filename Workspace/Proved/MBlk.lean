import Workspace.Impl.MBlkMain

/-!
# A minimal block system in polynomial time

Source: Luks, *Permutation groups and polynomial-time computation*, DIMACS 11 (1993), item (3.2),
p. 143, iterated as in [H, Section 2.1.2] ("By iterating the procedure, we will obtain a system
of minimal blocks in polynomial time"). This is Atkinson's method; the algorithm and its proof
are in `Workspace/Impl/MBlkMath.lean`, the program in `Workspace/Impl/MBlk*.lean`.

The program `GI.Impl.mblkProgram` has no primitives. On `encGroup gs` it returns a minimal
block system (`GI.Impl.mblk_main_spec`) at cost at most `2000000 * (wt + 1) ^ 8`, where `wt` is
the weight of the input. The bridge `GI.Lang.polyTimeAt_ofVal_of_lang_cells` turns this into a
machine program, with the cell bound `GI.Impl.cam_encGroup_cells`.
-/

namespace GI.Proved

open GI.Lang GI.Impl

/-- **A minimal block system of a transitive group can be found in polynomial time.** -/
theorem minimalBlocks : GI.Cited.MinimalBlocks :=
  polyTimeAt_ofVal_of_lang_cells mblkProgram 0 2000000 8 1 1
    (fun I => cam_encGroup_cells I.gs) mblk_main_spec

end GI.Proved
