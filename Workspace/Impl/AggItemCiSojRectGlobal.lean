module

public import Workspace.Impl.AggItemCiSojRectBudget

@[expose] public section

/-! # The certified rectangle branch at the common global cost -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The full rectangle branch meets the exact item postcondition with own cost
bounded by stage 66 of the common polynomial growth budget. -/
theorem itcs_rect_global (I : Iface) {Pg : Program} {Funs₀ : Funs} {A : itcsRectIdx}
    (hA : itcsRectOk Pg A) {e : Ω ≃ Fin k} {c : C → ℕ} {sv₀ lv : Val}
    (hcall : AsCall I Pg Funs₀ e c S sv₀ lv L) (K : ItSCtx k S L) (hK : K.OK e c)
    (hgood : Good P₀ .giant S) (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) (cf : RcCertFn)
    (b : Fin (P₀.κ+1) → Fin L.q) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) (hX : X.Good deltaB) (hx : x₀∈X.fiber)
    (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hlarge : ¬ (L.q : ℝ)≤(S.N : ℝ)^P₀.α)
    (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB))
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) (hcf : cf X (X.idx hx) hcert=cert)
    (E : Set (ItCfCh S L.toGiantLabels))
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R → RectRep P₀ S L.toGiantLabels W R)
    (hKeep : itcsKeep Pg A.rep Br cf e c K (.list []) E) (hE : E={(itcsChoices cf,rf)})
    (hRep : itcsRepFnOK Pg A.rep Br e K rf) :
    let inp := Val.list [.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []],
      itcqFV X,encFun (itcsBal X x₀),rcCertVal X (X.idx hx) cert]
    let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
    FunAll Pg A.f inp fun w cost =>
      ItCfIPost (itcsRel I Pg A.rep Br cf pf Bc hBc hBr) e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itcsSb e X Y x₀ y₀) B B w ∧
      cost≤(itcsGrow pf Bc Br hBc hBr)^[66] (I.inW .giant S+100) := by
  have run := itcs_rect_run I hA hcall K hK hgood pf Bc Br hBc hBr cf b X Y x₀ y₀ ho hX hx hp hb
    hlarge hcert cert hcf E rf hKeep hE hRep
  have bound := itcs_rect_own_stage I hA hcall hK pf Bc Br hBc hBr ho hx cert
  exact run.mono fun w cost ⟨hp,hc⟩ => ⟨hp,hc.trans bound⟩

end GI.Impl
