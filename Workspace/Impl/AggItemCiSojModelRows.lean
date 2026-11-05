module

public import Workspace.Impl.AggItemCiSojProcessA
public import Workspace.Impl.AggItemCiSojFO
public import Workspace.Impl.AggItemCiSojCCRows

@[expose] public section

/-! # The exact model output represented by the processed occurrence rows -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Keep the projected representative and its complete source generators for
every nonempty answer occurrence. -/
noncomputable def itcsNonemptyRows (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    List (permitted W R × List (permitted W R)) :=
  rows.filterMap fun row => row.2.map fun r => (row.1 * itcsRepMap rep r.1,r.2)

/-- Forget generator lists while retaining each query's own representative. -/
theorem itcs_nonempty_rows_reps (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    (itcsNonemptyRows rep rows).map Prod.fst =
      itcsAnswerReps rep (rows.map fun r => (r.1,r.2.map Prod.fst)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨t,r⟩
    cases r with
    | none => simpa only [itcsNonemptyRows,itcsAnswerReps,List.map_cons,List.filterMap_cons,
        Option.map_none] using ih
    | some r =>
      simpa only [itcsNonemptyRows,itcsAnswerReps,List.map_cons,List.filterMap_cons,
        Option.map_some,List.map_cons] using congrArg (List.cons (t*itcsRepMap rep r.1)) ih

/-- Model readers may select different representatives. Each encoded full-label
overcoset still equals the corresponding model overcoset. -/
theorem itcs_model_rows (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep))
    (hv : ∀ row ∈ rows, match row.2 with
      | none => (rep.state M N row.1).answer = ∅
      | some (g,_) => g.val ∈ (rep.state M N row.1).answer)
    (ms : List (Equiv.Perm (Fin L.q))) :
    List.Forall₂ (asOvAt L)
      ((itcsNonemptyRows rep rows).map fun r => (a₀ * r.1.val,leftGroup M,ms))
      ((rows.map fun r => (rep.query M N a₀ r.1).read (rep.state M N r.1).answer).reduceOption.map
        (AuxItem.liftOver L (leftGroup M))) := by
  induction rows with
  | nil => exact List.Forall₂.nil
  | cons row rows ih =>
    have hv0 := hv row (List.mem_cons_self ..)
    have htail := ih (fun r hr => hv r (List.mem_cons_of_mem _ hr))
    rcases row with ⟨t,r⟩
    cases r with
    | none =>
      have hread := itcs_query_read_none rep M N a₀ t hv0
      simpa only [itcsNonemptyRows,List.filterMap_cons,Option.map_none,List.map_cons,
        hread,List.reduceOption_cons_of_none] using htail
    | some r =>
      obtain ⟨g,sg⟩ := r
      obtain ⟨σ,hσ⟩ := itcs_query_read_some rep M N a₀ t g hv0
      simpa only [itcsNonemptyRows,List.filterMap_cons,Option.map_some,List.map_cons,
        hσ,List.reduceOption_cons_of_some] using
        List.Forall₂.cons (itcs_answer_ovAt rep M N a₀ t g hv0 hσ ms) htail

end GI.Impl
