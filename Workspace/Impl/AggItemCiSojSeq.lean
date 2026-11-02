import Workspace.Impl.AggItemCiSojModelOut

/-! # The exact continuation of the model's ordered rectangle queries -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Associativity for the model's script composition. -/
theorem itcs_bind_assoc {α β γ : Type} (s : Script α) (f : α → Script β) (g : β → Script γ) :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | done a => rfl
  | ask m T next ih =>
    change Script.ask m T (fun A => ((next A).bind f).bind g) =
      Script.ask m T (fun A => (next A).bind (fun a => (f a).bind g))
    exact congrArg (Script.ask m T) (funext ih)

/-- The remaining ordered queries, retaining the exact model-reader results
of earlier occurrences. -/
noncomputable def itcsQuerySeq (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (ts : List (permitted W R))
    (prev : List (Option (alternatingGroup (Fin L.q)))) : Script (Branches Ω) :=
  (Script.seqList (ts.map fun t => (rep.query M N a₀ t).script)).bind fun rest =>
    .done ⟨[],(prev++rest).reduceOption.map (AuxItem.liftOver L (leftGroup M))⟩

/-- No remaining query means the exact item is finished. -/
theorem itcs_query_seq_nil (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (prev : List (Option (alternatingGroup (Fin L.q)))) :
    itcsQuerySeq rep M N a₀ [] prev =
      .done ⟨[],prev.reduceOption.map (AuxItem.liftOver L (leftGroup M))⟩ := by
  simp only [itcsQuerySeq,List.map_nil,Script.seqList,Script.bind,List.append_nil]

/-- Ask the head occurrence and append its model-reader result before continuing.
This identity keeps repeated twists as distinct occurrences. -/
theorem itcs_query_seq_cons (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) (t : permitted W R) (ts : List (permitted W R))
    (prev : List (Option (alternatingGroup (Fin L.q)))) :
    itcsQuerySeq rep M N a₀ (t::ts) prev =
      .ask .cont (rep.state M N t) (fun A =>
        itcsQuerySeq rep M N a₀ ts (prev++[(rep.query M N a₀ t).read A])) := by
  have hq : (rep.query M N a₀ t).script =
      Script.ask .cont (rep.state M N t) (fun A => .done ((rep.query M N a₀ t).read A)) := rfl
  simp only [itcsQuerySeq,List.map_cons,Script.seqList,hq,Script.bind]
  apply congrArg (Script.ask .cont (rep.state M N t))
  funext A
  rw [itcs_bind_assoc]
  congr 1
  funext rest
  simp only [Script.bind,List.append_assoc,List.cons_append,List.nil_append]

/-- The initial query sequence is exactly the model's rectangle item script. -/
theorem itcs_query_seq_item (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q)) :
    (AuxItem.query (rep.queries M N a₀) (leftGroup M)).script =
      itcsQuerySeq rep M N a₀ (itcsTwists rep) [] := by
  simp only [AuxItem.script,itcs_twists_queries,List.map_map,itcsQuerySeq,List.nil_append,
    Function.comp_def]

end GI.Impl
