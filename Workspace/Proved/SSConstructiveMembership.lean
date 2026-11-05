module

public import Workspace.Impl.SSConstrWrap

@[expose] public section

/-!
# Constructive membership in polynomial time

`GI.Proved.constructiveMembership` proves `GI.Cited.ConstructiveMembership` by the deterministic
Schreier–Sims method (Furst, Hopcroft and Luks 1980; Knuth 1991; Seress 2003, Chapter 4). The
program builds a closed table for the base `[0, …, n-1]`, sifts `x`, and writes the table program,
the product of the used table entries, and one inversion (`GI.Impl.ssCmF_spec`). The output
exponent is `20`.
-/

namespace GI.Proved

open GI.Lang GI.Cited GI.Impl

/-- **Constructive membership** ([LM, Theorem 3.1(v)]), proved. -/
theorem constructiveMembership : GI.Cited.ConstructiveMembership :=
  ⟨20, polyTimeAt_ofVal_of_lang_cells (ssWrapProgram [ssCmF 51 29 19]) 52 (10 * ssPolyK) 32 1 1
    (fun I => ss_list_cells fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ss_encGroup_cells_le (by simp)
      · exact ss_encPerm_cells_le I.x (by simp))
    fun I => ssCmF_spec (ssWrapAt_of _) ((ssWrap_extra [ssCmF 51 29 19]).single) I.gs I.x I.mem⟩

end GI.Proved
