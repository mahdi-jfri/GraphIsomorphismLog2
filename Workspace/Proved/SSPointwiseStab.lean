import Workspace.Impl.SSStabWrap

/-!
# Pointwise stabilizers in polynomial time

`GI.Proved.pointwiseStab` proves `GI.Cited.PointwiseStab` by the deterministic Schreier–Sims
method (Furst, Hopcroft and Luks 1980; Knuth 1991; Seress 2003, Chapter 4). The table for the
base `S ++ [0, …, n-1]` is built, and the entries of the levels `≥ |S|` generate the pointwise
stabilizer of `S` (`GI.Proved.ss_stab_gens`, `GI.Impl.ssStabF_spec`).
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl

/-- **The pointwise stabilizer** ([LM, Theorem 3.1(iii)]), proved. -/
theorem pointwiseStab : GI.Cited.PointwiseStab :=
  polyTimeAt_ofVal_of_lang_cells (ssWrapProgram ssStabFuns) 56 (10 * ssPolyK) 32 1 1
    (fun I => ss_list_cells fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ss_encGroup_cells_le (by simp)
      · exact ss_encPts_cells_le I.S (gs := I.gs) (by simp) (by simp))
    fun I => ssStabF_spec ssStabAt_of I.gs I.S

end GI.Proved
