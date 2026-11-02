import Workspace.Impl.AggItemCiSojStepNext

/-! # The complete actual first-rectangle step program -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

/-- The actual queue program meets the full item step contract in every reachable
state. Its at-most-two-query protocol uses the exact full finalizer and the same
fixed choices throughout. All cost and output weights fit `itcsXs`. -/
theorem itcs_rel_step (I : Iface) {Pg : Program} {fr fk fin : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn}
    (pf : Prim) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hf : Pg.funs[fk]? = some (itcsQueueF fin)) (hfin : itcsFinalSpec Pg fin pf)
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (hK : K.OK e c) (hgood : Good P₀ .giant S)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q) (ist : Val)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)) (f : ℕ)
    (h : (itcsRel I Pg fr Br cf pf Bc hBc hBr).Ri e c S L K b oX oY ist E sb f) :
    FunAll Pg fk ist fun w cost => cost≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) ∧
      ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b oX oY E sb f
        (itcsXs pf Bc Br hBc hBr (I.inW .giant S)) w := by
  obtain ⟨hKeep,F,hcap,hInside⟩ := h
  rcases hInside with ⟨u,hu,heq,htrace,hfuel⟩ | ⟨t,u₀,u₁,ht,h₀,h₁,heq,htrace⟩
  · subst ist
    cases ht : F.rep.twist with
    | none =>
      have hcan : List.Forall₂ (fun t v => AnsC e v (F.rep.state F.M F.N t).answer) [1] [u] :=
        .cons hu .nil
      have hcanon : List.Forall₂ (fun t v => AnsC e v (F.rep.state F.M F.N t).answer)
          (itcsTwists F.rep) ([]++[u]) := by
        simpa only [itcsTwists,ht,Option.toList_none,List.nil_append] using hcan
      have hstate : (Val.list [.list [F.payload,.list [],.list []],u]).wt≤ F.weight := by
        simpa only [itcsQFrame.state0,itcsQFrame.pending,ht,Option.toList_none,List.map_nil] using F.state0_wt u hu.wt_le
      have hs : ∀ ch∈E, sb ch=.done F.result := fun ch hch => (htrace ch hch).trans (F.done_none ht)
      have result := itcs_rel_finish I pf hBc hBr hf hfin e c S L K b oX oY E sb f F [] u
        hKeep hcap hcanon hstate (F.final1_wt u hu.wt_le) hs
      simpa only [itcsQFrame.state0,itcsQFrame.pending,ht,Option.toList_none,List.map_nil] using result
    | some t =>
      have hs : ∀ ch∈E, sb ch=itcsQuerySeq F.rep F.M F.N F.a₀ [t] [F.read 1] := by
        intro ch hch
        simpa only [ht,Option.toList_some] using htrace ch hch
      have hn : 1≤ f := by simpa only [ht,Option.toList_some,List.length_cons,List.length_nil] using hfuel
      exact itcs_rel_next I pf hBc hBr hf e c S L K hK hgood b oX oY E sb f F t ht u hu hKeep hcap hs hn
  · subst ist
    have hcan : List.Forall₂ (fun t v => AnsC e v (F.rep.state F.M F.N t).answer) [1,t] [u₀,u₁] :=
      .cons h₀ (.cons h₁ .nil)
    have hcanon : List.Forall₂ (fun t v => AnsC e v (F.rep.state F.M F.N t).answer)
        (itcsTwists F.rep) ([u₀]++[u₁]) := by
      simpa only [itcsTwists,ht,Option.toList_some,List.cons_append,List.nil_append] using hcan
    exact itcs_rel_finish I pf hBc hBr hf hfin e c S L K b oX oY E sb f F [u₀] u₁
      hKeep hcap hcanon (F.state1_wt u₀ u₁ h₀.wt_le h₁.wt_le) (F.final2_wt u₀ u₁ h₀.wt_le h₁.wt_le) htrace

end GI.Impl
