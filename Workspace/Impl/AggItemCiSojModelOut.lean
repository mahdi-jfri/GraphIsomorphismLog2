import Workspace.Impl.AggItemCiSojModelRows

/-! # The final item output represented by all processed rectangle answers -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (gens)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Full-label overcosets in the order of the nonempty query occurrences. -/
noncomputable def itcsRowsOut (rep : RectRep P₀ S L W R) (M : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep)) (ms : List (Perm (Fin L.q))) :
    List (LcOver L.q) :=
  (itcsNonemptyRows rep rows).map fun r => (a₀*r.1.val,leftGroup M,ms)

/-- The actual model readers applied to the complete exact physical answers. -/
noncomputable def itcsRowsModel (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep)) : Branches Ω :=
  ⟨[],(rows.map fun r => (rep.query M N a₀ r.1).read (rep.state M N r.1).answer).reduceOption.map
    (AuxItem.liftOver L (leftGroup M))⟩

/-- Exact model overcosets and the reconstructed full source group give the full
item-output relation. The empty result imposes no unnecessary group hypothesis. -/
theorem itcs_rows_out (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep))
    (hv : ∀ row ∈ rows, match row.2 with
      | none => (rep.state M N row.1).answer = ∅
      | some (g,_) => g.val ∈ (rep.state M N row.1).answer)
    (ms : List (Perm (Fin L.q)))
    (hg : itcsNonemptyRows rep rows ≠ [] →
      gens ms = (leftGroup M).map (alternatingGroup (Fin L.q)).subtype) :
    ItSOut e L (itcsRowsModel rep M N a₀ rows) [] (itcsRowsOut rep M a₀ rows ms) := by
  refine ⟨itcs_model_rows rep M N a₀ rows hv ms,rfl,?_,?_⟩
  · intro i hi
    exact False.elim (Nat.not_lt_zero _ hi)
  · intro o ho
    obtain ⟨r,hr,rfl⟩ := List.mem_map.1 ho
    exact hg (by intro he; simpa only [he,List.not_mem_nil] using hr)

end GI.Impl
