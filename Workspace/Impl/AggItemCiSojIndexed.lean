import Workspace.Impl.AggItemCiSojAnswers
import Workspace.Impl.AggItemCiSojSeq

/-! # Retaining exact query order in the saved-answer map -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- One typed result for each saved-answer index, with that occurrence's twist. -/
noncomputable def itcsIndexedRows (rep : RectRep P₀ S L W R) (ts : List (permitted W R))
    (answers : List Val) (ht : ts.length=answers.length)
    (rs : Fin answers.length → itcsProcessRow rep) : List (permitted W R × itcsProcessRow rep) :=
  (List.finRange answers.length).map fun i => (ts[i.val]'(by simpa only [ht] using i.isLt),rs i)

/-- The typed rows retain all twists, including repetitions, in their exact order. -/
theorem itcs_indexed_order (rep : RectRep P₀ S L W R) (ts : List (permitted W R))
    (answers : List Val) (ht : ts.length=answers.length) (rs : Fin answers.length → itcsProcessRow rep) :
    (itcsIndexedRows rep ts answers ht rs).map Prod.fst=ts := by
  apply List.ext_getElem
  · simpa only [itcsIndexedRows,List.length_map,List.length_finRange] using ht.symm
  · intro i hi hj
    simp only [itcsIndexedRows,List.getElem_map,List.getElem_finRange]
    rfl

/-- Every typed occurrence carries the exact result established by its callback. -/
theorem itcs_indexed_valid (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (ts : List (permitted W R)) (answers : List Val) (ht : ts.length=answers.length)
    (rs : Fin answers.length → itcsProcessRow rep)
    (hv : ∀ i, itcsProcessValid rep M N (ts[i.val]'(by simpa only [ht] using i.isLt)) (rs i)) :
    ∀ row∈itcsIndexedRows rep ts answers ht rs, itcsProcessValid rep M N row.1 row.2 := by
  intro row hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hr
  exact hv i

/-- The actual callback-value list is exactly the encoding of the indexed rows. -/
theorem itcs_indexed_code (rep : RectRep P₀ S L W R) (ts : List (permitted W R))
    (answers : List Val) (ht : ts.length=answers.length) (rs : Fin answers.length → itcsProcessRow rep) :
    (itcsIndexedRows rep ts answers ht rs).map (fun r => itcsProcessRowVal rep r.1 r.2) =
      (List.finRange answers.length).map (fun i =>
        itcsProcessRowVal rep (ts[i.val]'(by simpa only [ht] using i.isLt)) (rs i)) := by
  simp only [itcsIndexedRows,List.map_map,Function.comp_def]

/-- The model result depends on the occurrence order and exact answers, while
the selected canonical representatives may differ from the model readers. -/
theorem itcs_rows_model_of_order (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (rows : List (permitted W R × itcsProcessRow rep))
    (ts : List (permitted W R)) (ht : rows.map Prod.fst=ts) :
    itcsRowsModel rep M N a₀ rows =
      ⟨[],(ts.map fun t => (rep.query M N a₀ t).read (rep.state M N t).answer).reduceOption.map
        (AuxItem.liftOver L (leftGroup M))⟩ := by
  rw [←ht]
  simp only [itcsRowsModel,List.map_map,Function.comp_def]

/-- The exact result of the model's whole ordered query item. -/
theorem itcs_query_seq_eval (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (ts : List (permitted W R)) :
    (itcsQuerySeq rep M N a₀ ts []).evalExact =
      ⟨[],(ts.map fun t => (rep.query M N a₀ t).read (rep.state M N t).answer).reduceOption.map
        (AuxItem.liftOver L (leftGroup M))⟩ := by
  simp only [itcsQuerySeq,Script.evalExact_bind,Script.evalExact_seqList,List.map_map,
    Function.comp_def,AuxQuery.script_evalExact,List.nil_append,Script.evalExact]
  rfl

end GI.Impl
