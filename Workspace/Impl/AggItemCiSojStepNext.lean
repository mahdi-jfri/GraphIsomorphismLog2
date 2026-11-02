import Workspace.Impl.AggItemCiSojStepFinish

/-! # The actual queue's optional second query and its exact continuation -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

/-- Ask the recorded second occurrence, retaining the entire first canonical
answer. The next state is exactly the second reachable protocol state. -/
theorem itcs_rel_next (I : Iface) {Pg : Program} {fr fk fin : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn}
    (pf : Prim) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hf : Pg.funs[fk]? = some (itcsQueueF fin))
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (hK : K.OK e c) (hgood : Good P₀ .giant S)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)) (f : ℕ)
    (F : itcsQFrame e S L.toGiantLabels) (t : permitted F.W F.R) (ht : F.rep.twist=some t)
    (u : Val) (hu : AnsC e u (F.rep.state F.M F.N 1).answer)
    (hKeep : itcsKeep Pg fr Br cf e c K (.list []) E)
    (hcap : F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100))
    (htrace : ∀ ch∈E, sb ch=itcsQuerySeq F.rep F.M F.N F.a₀ [t] [F.read 1]) (hfuel : 1≤ f) :
    FunAll Pg fk (F.state0 u) fun w cost => cost≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) ∧
      ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b oX oY E sb f
        (itcsXs pf Bc Br hBc hBr (I.inW .giant S)) w := by
  let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
  let kst := Val.list [F.payload,.list [],.list [u]]
  let output := Val.list [.nat 1,.nat 1,F.query t,kst]
  have hstate : (Val.list [.list [F.payload,.list [F.query t],.list []],u]).wt≤ F.weight := by
    simpa only [itcsQFrame.state0,itcsQFrame.pending,ht,Option.toList_some,List.map_cons,List.map_nil] using F.state0_wt u hu.wt_le
  rcases itcs_queue_input_parts F.payload [F.query t] [] u hstate with ⟨hp,hn,ha,hw⟩
  have hC := itcs_queue_global pf Bc Br hBc hBr (I.inW .giant S) F.weight hcap
    F.payload [F.query t] [] u hp hn ha hw (Cf:=0) (Nat.zero_le _)
  have prog : FunDet Pg fk (F.state0 u) output (100*(itcsQueueW F.payload [F.query t] [] u 0+1)) := by
    simpa only [itcsQFrame.state0,itcsQFrame.pending,ht,Option.toList_some,List.map_cons,List.map_nil,
      List.nil_append,modeCode,output,kst] using itcs_queue_next F.payload (F.query t) u [] hf
  have hpost : ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b oX oY E sb f B output := by
    apply itcs_query_post (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c K b oX oY E sb f B
      F.rep F.M F.N F.a₀ t [] [F.read 1] F.hs F.hier kst hK hgood F.conds.2.2.1 F.conds.2.2.2.1
      F.hhs F.hlen F.hhier (by omega) (itcs_keep_ne hKeep) htrace
    intro u₁ h₁
    refine ⟨hKeep,F,hcap,Or.inr ⟨t,u,u₁,ht,hu,h₁,rfl,?_⟩⟩
    intro ch hch
    change itcsQuerySeq F.rep F.M F.N F.a₀ [] [F.read 1,F.read t] = .done F.result
    exact F.done_some t ht
  refine FunAll.mono prog ?_
  intro w cost hh
  obtain ⟨he,hcost⟩ := hh
  rw [he]
  exact ⟨hcost.trans hC,hpost⟩

end GI.Impl
