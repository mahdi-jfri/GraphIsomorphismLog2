import Workspace.Impl.SSMember

/-!
# Membership in polynomial time

`GI.Proved.membership` proves `GI.Cited.Membership` by the deterministic Schreier–Sims method
(Furst, Hopcroft and Luks 1980; Knuth 1991; Seress 2003, Chapter 4). The program builds a closed
table for the base `[0, …, n-1]` and sifts `x` (`GI.Impl.ssMemF_spec`).
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl

/-- **Membership** ([LM, Theorem 3.1(v)]), proved. -/
theorem membership : GI.Cited.Membership :=
  polyTimeAt_ofVal_of_lang_cells (ssWrapProgram [ssMemF 51]) 52 (10 * ssPolyK) 32 1 1
    (fun I => ss_list_cells fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ss_encGroup_cells_le (by simp)
      · exact ss_encPerm_cells_le I.x (by simp))
    fun I => ssMemF_spec (ssWrapAt_of _) ((ssWrap_extra [ssMemF 51]).single) I.gs I.x

end GI.Proved
