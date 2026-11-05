module

public import Workspace.Impl.AggItemCiSojModelRows

@[expose] public section

/-! # Filtering the actual encodings of the processed occurrence rows -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The ordinary optional pair encoded by each processed occurrence. -/
noncomputable def itcsRowsOptions (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    List (Option (Perm (Fin L.q) × List (Perm (Fin L.q)))) :=
  rows.map fun row => row.2.map fun r =>
    ((row.1 * itcsRepMap rep r.1).val.val,r.2.map fun g => g.val.val)

/-- The surviving byte rows are precisely the nonempty typed rows. -/
theorem itcs_rows_options_reduce (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    (itcsRowsOptions rep rows).reduceOption =
      (itcsNonemptyRows rep rows).map fun r => (r.1.val.val,r.2.map fun g => g.val.val) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    rcases r with ⟨t,r⟩
    simp only [itcsRowsOptions,itcsNonemptyRows] at ih
    cases r <;> simp only [itcsRowsOptions,itcsNonemptyRows,List.map_cons,
      Option.map_none,Option.map_some,List.filterMap_cons,List.reduceOption_cons_of_none,
      List.reduceOption_cons_of_some,List.map_cons,ih]

/-- Encoding all optional rows agrees with the actual projector's output. -/
theorem itcs_rows_options_code (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    (itcsRowsOptions rep rows).map itcsRowVal =
      rows.map fun r => itcsProcessRowVal rep r.1 r.2 := by
  simp only [itcsRowsOptions,itcsProcessRowVal,List.map_map,Function.comp_def]

/-- Filtering the exact projected bytes keeps the nonempty typed rows in order. -/
theorem itcs_processed_filter {Pg : Program} {flt f : ℕ}
    (hh : Pg.HasAt flt (filterFuns flt f)) (hf : Pg.funs[f]? = some itcsRowNE)
    (rep : RectRep P₀ S L W R) (rows : List (permitted W R × itcsProcessRow rep)) :
    let inp := Val.list [.nat 0,.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2)]
    FunDet Pg flt inp
      (.list ((itcsNonemptyRows rep rows).map fun r =>
        .list [encPerm r.1.val.val,encGroup (r.2.map fun g => g.val.val)]))
      (rows.length*(100*(inp.wt+10))+loopModK*(rows.length+1)*(2*inp.wt+rows.length+1)) := by
  have hp := itcs_row_filter hh hf (itcsRowsOptions rep rows)
  rw [itcs_rows_options_code,itcs_rows_options_reduce] at hp
  simpa only [List.map_map,Function.comp_def,itcsRowVal,itcsRowsOptions,List.length_map] using hp

end GI.Impl
