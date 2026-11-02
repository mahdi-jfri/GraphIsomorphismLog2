import Workspace.Impl.AggItemCiSojRes
import Workspace.Impl.AggItemCiSojSpec
import Workspace.Impl.AggItemCiSojWt

/-! # Returning an exact finished first-rectangle item to the aggregation stage -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The bare output occurs as a subvalue of the finished-item result, so its
weight is already paid for by the actual finished program. -/
theorem itcs_out_weight_le (os : List (LcOver L.q)) :
    (itSOutV ([] : List (Perm (Fin k) × Acc k)) os).wt ≤
      (itcsResV (itciOV os)).wt := by
  have hprefix : (Val.list [.list [],itciOV os]).wt ≤
      (Val.list [.list [],itciOV os,.list []]).wt :=
    wt_list_mono ⟨[.list []],rfl⟩
  exact hprefix.trans (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- An exact finished script and exact output encoding meet the item's post
contract while keeping the same fixed choice set. -/
theorem itcs_done_post (R : ItCfIRel) (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω))
    (f B : ℕ) (ovs : List (Perm Ω × Subgroup (Perm Ω))) (os : List (LcOver L.q))
    (hK : R.Ki e c S L K (.list []) E)
    (hs : ∀ ch ∈ E, sb ch = .done ⟨[],ovs⟩)
    (ho : ItSOut e L.toGiantLabels ⟨[],ovs⟩ [] os)
    (hw : (itSOutV ([] : List (Perm (Fin k) × Acc k)) os).wt ≤ B) :
    ItCfIPost R e c S L K b oX oY E sb f B (itcsResV (itciOV os)) := by
  exact Or.inl ⟨⟨[],ovs⟩,[],os,.list [],E,rfl,subset_rfl,hs,hK,ho,hw⟩

/-- The actual finished program pays for its output. Its own cost bound therefore
discharges the output-weight clause of the full aggregation postcondition. -/
theorem itcs_done_funall {Pg : Program} {fn Cb B f : ℕ} (R : ItCfIRel)
    (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω))
    (ovs : List (Perm Ω × Subgroup (Perm Ω))) (os : List (LcOver L.q)) (inp : Val)
    (hK : R.Ki e c S L K (.list []) E)
    (hs : ∀ ch ∈ E, sb ch = .done ⟨[],ovs⟩)
    (ho : ItSOut e L.toGiantLabels ⟨[],ovs⟩ [] os)
    (hp : FunDet Pg fn inp (itcsResV (itciOV os)) Cb) (hb : Cb ≤ B) :
    FunAll Pg fn inp fun w cost => cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E sb f B w := by
  have hw := (itcs_out_weight_le (k:=k) os).trans ((itcs_det_weight hp).trans hb)
  refine FunAll.mono hp ?_
  intro w cost hh
  obtain ⟨he,hc⟩ := hh
  rw [he]
  exact ⟨hc.trans hb,itcs_done_post R e c K b oX oY E sb f B ovs os hK hs ho hw⟩

end GI.Impl
