module

public import Workspace.Impl.AggItemCiSojRel
public import Workspace.Impl.AggItemCiSojDone

@[expose] public section

/-! # The actual queue's finalizing step satisfies the full item postcondition -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

/-- Finalize a complete canonical answer buffer. Every finalizer precondition
comes from the frame's exact query order, and every queue-cost premise comes
from its actual encoded input. -/
theorem itcs_rel_finish (I : Iface) {Pg : Program} {fr fk fin : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn}
    (pf : Prim) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hf : Pg.funs[fk]? = some (itcsQueueF fin)) (hfin : itcsFinalSpec Pg fin pf)
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)) (f : ℕ)
    (F : itcsQFrame e S L.toGiantLabels) (history : List Val) (u : Val)
    (hKeep : itcsKeep Pg fr Br cf e c K (.list []) E)
    (hcap : F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100))
    (hcanon : List.Forall₂ (fun t v => AnsC e v (F.rep.state F.M F.N t).answer)
      (itcsTwists F.rep) (history++[u]))
    (hstate : (Val.list [.list [F.payload,.list [],.list history],u]).wt≤ F.weight)
    (hargs : (Val.list [F.payload,.list (history++[u])]).wt≤ F.weight)
    (hscript : ∀ ch∈E, sb ch=.done F.result) :
    FunAll Pg fk (.list [.list [F.payload,.list [],.list history],u]) fun w cost =>
      cost≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) ∧
        ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b oX oY E sb f
          (itcsXs pf Bc Br hBc hBr (I.inW .giant S)) w := by
  obtain ⟨os,hfinal,hout⟩ := F.finalize hfin (history++[u]) hcanon
  have result := itcs_queue_final F.payload u (itcsResV (itciOV os)) history hf hfinal
  rcases itcs_queue_input_parts F.payload [] history u hstate with ⟨hp,hn,ha,hu⟩
  have hC := itcs_queue_global pf Bc Br hBc hBr (I.inW .giant S) F.weight hcap
    F.payload [] history u hp hn ha hu (itcs_final_cost_next pf Bc Br hBc hBr hargs)
  exact itcs_done_funall (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c K b oX oY E sb F.overs os
    (.list [.list [F.payload,.list [],.list history],u]) hKeep hscript hout result hC

end GI.Impl
