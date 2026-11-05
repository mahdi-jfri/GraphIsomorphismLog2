module

public import Workspace.Impl.AggItemCiSojFrameBudget
public import Workspace.Impl.AggItemCiSojInit
public import Workspace.Impl.AggItemCiSojBudgetCtx

@[expose] public section

/-! # The two reachable states of the first-rectangle item protocol -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

/-- The first received answer, or the second received answer after the recorded
optional twist. Canonical values retain their full encoded generator lists. -/
def itcsInside {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
    (F : itcsQFrame e S L) (ist : Val) (E : Set (ItCfCh S L))
    (sb : ItCfCh S L → Script (Branches Ω)) (f : ℕ) : Prop :=
  (∃ u, AnsC e u (F.rep.state F.M F.N 1).answer ∧ ist=F.state0 u ∧
    (∀ ch∈E, sb ch=itcsQuerySeq F.rep F.M F.N F.a₀ F.rep.twist.toList [F.read 1]) ∧
      F.rep.twist.toList.length≤ f) ∨
  (∃ (t : permitted F.W F.R) (u₀ u₁ : Val), F.rep.twist=some t ∧
    AnsC e u₀ (F.rep.state F.M F.N 1).answer ∧ AnsC e u₁ (F.rep.state F.M F.N t).answer ∧
      ist=F.state1 u₀ u₁ ∧ ∀ ch∈E, sb ch=.done F.result)

/-- The item relation retains one fixed choice set and one frame. Its byte-value
bound leaves two analysis stages for processing either continuation state. -/
def itcsRel (I : Iface) (Pg : Program) (fr : ℕ) (Br : ℕ → ℕ) (cf : RcCertFn)
    (pf : Prim) (Bc : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) : ItCfIRel where
  Ki := fun e c _S _L K w E => itcsKeep Pg fr Br cf e c K w E
  Ri := fun e c S L K _b _oX _oY ist E sb f =>
    itcsKeep Pg fr Br cf e c K (.list []) E ∧
      ∃ F : itcsQFrame e S L.toGiantLabels,
        F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100) ∧ itcsInside F ist E sb f

/-- Every reachable encoded item state meets the same global polynomial bound. -/
theorem itcs_rel_wtR (I : Iface) {Pg : Program} {fr : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn} (pf : Prim)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {K : ItSCtx k S L} {b : Fin (P₀.κ+1) → Fin L.q} {oX oY : CfgOut L.q} {ist : Val}
    {E : Set (ItCfCh S L.toGiantLabels)} {sb : ItCfCh S L.toGiantLabels → Script (Branches Ω)} {f : ℕ}
    (h : (itcsRel I Pg fr Br cf pf Bc hBc hBr).Ri e c S L K b oX oY ist E sb f) :
    ist.wt≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) := by
  obtain ⟨-,F,hcap,hi⟩ := h
  have hb := hcap.trans (itcs_budget_iter_le pf Bc Br hBc hBr (I.inW .giant S) (i:=126) (by decide))
  rcases hi with ⟨u,hu,rfl,-,-⟩ | ⟨t,u₀,u₁,-,h₀,h₁,rfl,-⟩
  · exact (F.state0_wt u hu.wt_le).trans hb
  · exact (F.state1_wt u₀ u₁ h₀.wt_le h₁.wt_le).trans hb

/-- The initial exact query request enters the first reachable continuation
state for every canonical answer. -/
theorem itcs_rel_enter (I : Iface) {Pg : Program} {fr : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn} (pf : Prim)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (K : ItSCtx k S L) (hK : K.OK e c) (hg : Good P₀ .giant S)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω))
    (F : itcsQFrame e S L.toGiantLabels)
    (hKeep : itcsKeep Pg fr Br cf e c K (.list []) E)
    (hcap : F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100))
    (hs : ∀ ch∈E, sb ch=itcsQuerySeq F.rep F.M F.N F.a₀ (itcsTwists F.rep) []) :
    ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b oX oY E sb
      (itcsXs pf Bc Br hBc hBr (I.inW .giant S)) (itcsXs pf Bc Br hBc hBr (I.inW .giant S))
      (itcsAskV (F.query 1) F.payload (.list F.pending)) := by
  let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
  have hb := itcs_budget_input pf Bc Br hBc hBr (I.inW .giant S)
  have h2 : 2≤ B := by dsimp only [B]; omega
  have hn : F.rep.twist.toList.length≤1 := by cases F.rep.twist <;> simp
  apply itcs_query_post (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c K b oX oY E sb B B
    F.rep F.M F.N F.a₀ 1 F.rep.twist.toList [] F.hs F.hier
    (.list [F.payload,.list F.pending,.list []]) hK hg F.conds.2.2.1 F.conds.2.2.2.1
    F.hhs F.hlen F.hhier (by omega) (itcs_keep_ne hKeep) hs
  intro u hu
  refine ⟨hKeep,F,hcap,Or.inl ⟨u,hu,rfl,?_,?_⟩⟩
  · intro ch hch
    rfl
  · omega

end GI.Impl
