module

public import Workspace.Impl.AggItemCiSojFinalSpec
public import Workspace.Impl.AggItemCiSojQueryPost

@[expose] public section

/-! # The fixed semantic and encoded data of one rectangle continuation -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- All data fixed before the first query. The representation, matrices, and
alignment stay unchanged while canonical representatives arrive. -/
structure itcsQFrame {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S) where
  W : Finset (Fin L.q)
  R : Finset (Fin L.q)
  conds : RectConds P₀ S L W R
  rep : RectRep P₀ S L W R
  M : W → R → Bool
  N : W → R → Bool
  a₀ : alternatingGroup (Fin L.q)
  hs : List (Perm (Fin k) × Perm (Fin L.q))
  hhs : PairGens e L rep.H hs
  hlen : hs.length≤ k^2
  hier : Val
  hhier : HierValC e hier S.hier

namespace itcsQFrame

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
  (F : itcsQFrame e S L)

/-- The actual encoded inherited query for one recorded twist. -/
noncomputable def query (t : permitted F.W F.R) : Val := itcsQVal e F.rep F.M F.N t F.hs F.hier

/-- The common payload retained until all answers have arrived. -/
noncomputable def payload : Val :=
  .list [.nat L.q,encPerm F.a₀.val,
    .list ((itciMs (itcsFixColor F.W) (itciOt (itcsFixColor F.W))).map encPerm),
    liftLabCtx L.q k (F.hs.map Prod.swap),
    .list ((itcsTwists F.rep).map fun t => encPerm t.val.val)]

/-- Query occurrences and the optional pending second state. -/
noncomputable def queries : List Val := (itcsTwists F.rep).map F.query
noncomputable def pending : List Val := F.rep.twist.toList.map F.query

/-- The model reader's exact value for one occurrence. -/
noncomputable def read (t : permitted F.W F.R) : Option (alternatingGroup (Fin L.q)) :=
  (F.rep.query F.M F.N F.a₀ t).read (F.rep.state F.M F.N t).answer

/-- The exact model output after every recorded occurrence. -/
noncomputable def overs : List (Perm Ω × Subgroup (Perm Ω)) :=
  ((itcsTwists F.rep).map F.read).reduceOption.map (AuxItem.liftOver L (leftGroup F.M))
noncomputable def result : Branches Ω := ⟨[],F.overs⟩

/-- A common byte-value budget for the two continuation states and their
complete canonical-answer finalizer input. -/
noncomputable def weight : ℕ := 1000*(F.payload.wt+(Val.list F.queries).wt+ansW k+100)

/-- There are precisely the untwisted and optional twisted occurrences. -/
theorem queries_cons : F.queries=F.query 1::F.pending := rfl

/-- No pending twist means the first answer already finishes the model item. -/
theorem done_none (h : F.rep.twist=none) :
    itcsQuerySeq F.rep F.M F.N F.a₀ F.rep.twist.toList [F.read 1] = .done F.result := by
  simp only [h,Option.toList_none,itcs_query_seq_nil,result,overs,itcsTwists,
    List.map_cons,List.map_nil,List.reduceOption_cons_of_none]

/-- The second exact answer finishes the model item, including identity twists. -/
theorem done_some (t : permitted F.W F.R) (h : F.rep.twist=some t) :
    itcsQuerySeq F.rep F.M F.N F.a₀ [] [F.read 1,F.read t] = .done F.result := by
  simp only [itcs_query_seq_nil,result,overs,itcsTwists,h,Option.toList_some,
    List.map_cons,List.map_nil]

/-- The recorded model result is exactly the whole query item's exact result. -/
theorem result_eq_eval : F.result =
    (AuxItem.query (F.rep.queries F.M F.N F.a₀) (leftGroup F.M)).script.evalExact := by
  rw [itcs_query_seq_item,itcs_query_seq_eval]
  rfl

/-- The complete proved finalizer applies directly to this retained payload. -/
theorem finalize {Pg : Program} {fin : ℕ} {pf : Prim} (hf : itcsFinalSpec Pg fin pf)
    (answers : List Val)
    (ha : List.Forall₂ (fun t u => AnsC e u (F.rep.state F.M F.N t).answer) (itcsTwists F.rep) answers) :
    ∃ os, FunDet Pg fin (.list [F.payload,.list answers]) (itcsResV (itciOV os))
      (itcsFinalC pf (Val.list [F.payload,.list answers]).wt) ∧ ItSOut e L F.result [] os := by
  rw [F.result_eq_eval]
  exact hf e S L F.W F.R F.rep F.M F.N F.a₀ F.hs F.hhs answers ha

end itcsQFrame
end GI.Impl
