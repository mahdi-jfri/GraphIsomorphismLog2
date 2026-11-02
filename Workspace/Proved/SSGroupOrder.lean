import Workspace.Impl.SSOrderWrap

/-!
# The order of a group in polynomial time

`GI.Proved.groupOrder` proves `GI.Cited.GroupOrder` by the deterministic Schreier–Sims method
(Furst, Hopcroft and Luks 1980; Knuth 1991; Seress 2003, Chapter 4). The order is the product,
over the levels of a closed table, of one plus the number of entries of the level
(`GI.Proved.ss_card_gens`, `GI.Impl.ssOrdF_spec`).
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl

/-- **The order of a group** ([LM, Theorem 3.1(iv)]), proved. -/
theorem groupOrder : GI.Cited.GroupOrder :=
  polyTimeAt_ofVal_of_lang_cells (ssWrapProgram ssOrdFuns) 60 (10 * ssPolyK) 32 1 1
    (fun I => cam_encGroup_cells I.gs) fun I => ssOrdF_spec ssOrdAt_of I.gs

end GI.Proved
