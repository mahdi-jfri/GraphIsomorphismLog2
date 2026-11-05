module

public import Workspace.Impl.AggItemCiSojFrameScript
public import Workspace.Impl.AggItemCiSojRel
public import Workspace.Impl.AggItemCiSojDone

@[expose] public section

/-! # Both certified rectangle outcomes satisfy the aggregation postcondition -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- A successful literal guard enters the exact two-query relation using the
same singleton set of globally fixed choices returned by init. -/
theorem itcs_cert_enter (I : Iface) {Pg : Program} {fr : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn}
    (pf : Prim) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L) (hK : K.OK e c) (hgood : Good P₀ .giant S)
    (b : Fin (P₀.κ+1) → Fin L.q) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (E : Set (ItCfCh S L.toGiantLabels))
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R → RectRep P₀ S L.toGiantLabels W R)
    (hKeep : itcsKeep Pg fr Br cf e c K (.list []) E) (hE : E={(itcsChoices cf,rf)})
    (hx : x₀∈X.fiber) (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB))
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) (hcf : cf X (X.idx hx) hcert=cert)
    (hg : itcsRectGuard X Y y₀ (X.idx hx) cert)
    (hc : RectConds P₀ S L.toGiantLabels (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L.toGiantLabels (rf _ _ hc).H hs)
    (hlen : hs.length≤ k^2) (hier : Val) (hhier : HierValC e hier S.hier)
    (hcap : (itcsFrameOf hc (rf _ _ hc) X Y (certVals X (X.idx hx) cert).2.2
      (itcsCertAlign X Y y₀ (X.idx hx) cert hg) hs hhs hlen hier hhier).weight ≤
        (itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100)) :
    let F := itcsFrameOf hc (rf _ _ hc) X Y (certVals X (X.idx hx) cert).2.2
      (itcsCertAlign X Y y₀ (X.idx hx) cert hg) hs hhs hlen hier hhier
    let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
    ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b (.pair X x₀) (.pair Y y₀) E
      (itcsSb e X Y x₀ y₀) B B (itcsAskV (F.query 1) F.payload (.list F.pending)) := by
  dsimp only
  apply itcs_rel_enter I pf hBc hBr e c S L K hK hgood b (.pair X x₀) (.pair Y y₀) E
    (itcsSb e X Y x₀ y₀) _ hKeep hcap
  intro ch hch
  rw [hE,Set.mem_singleton_iff] at hch
  subst ch
  exact itcs_frame_script cf rf X Y x₀ y₀ hx hp hb hcert cert hcf hg hc hs hhs hlen hier hhier

/-- A failed literal rectangle guard returns the empty finished result and
retains the same fixed choice set. -/
theorem itcs_cert_skip_post (I : Iface) {Pg : Program} {fr : ℕ} {Br Bc : ℕ → ℕ} {cf : RcCertFn}
    (pf : Prim) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L)
    (b : Fin (P₀.κ+1) → Fin L.q) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (E : Set (ItCfCh S L.toGiantLabels))
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L.toGiantLabels W R → RectRep P₀ S L.toGiantLabels W R)
    (hKeep : itcsKeep Pg fr Br cf e c K (.list []) E) (hE : E={(itcsChoices cf,rf)})
    (hx : x₀∈X.fiber) (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB))
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) (hcf : cf X (X.idx hx) hcert=cert)
    (hg : ¬ itcsRectGuard X Y y₀ (X.idx hx) cert) :
    let B := itcsXs pf Bc Br hBc hBr (I.inW .giant S)
    ItCfIPost (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c S L K b (.pair X x₀) (.pair Y y₀) E
      (itcsSb e X Y x₀ y₀) B B (itcsResV (.list [])) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  dsimp only
  apply itcs_done_post (itcsRel I Pg fr Br cf pf Bc hBc hBr) e c K b (.pair X x₀) (.pair Y y₀) E
    (itcsSb e X Y x₀ y₀) _ _ [] [] hKeep
  · intro ch hch
    rw [hE,Set.mem_singleton_iff] at hch
    subst ch
    change (sojItem (RectOracle.ofReps rf) (itcsChoices cf) X Y x₀ y₀).script = _
    rw [itcs_cert_script _ _ X Y x₀ y₀ hx hp hb hcert]
    simp only [itcs_choices_cert]
    rw [hcf]
    exact itcs_rect_skip _ _ X Y y₀ (X.idx hx) cert hg
  · simp [ItSOut]
  · have hb := itcs_budget_input pf Bc Br hBc hBr (I.inW .giant S)
    have hw : (itSOutV ([] : List (Perm (Fin k) × Acc k)) ([] : List (LcOver L.q))).wt ≤ 100 := by
      simp only [itSOutV,List.map_nil]
      decide
    omega

end GI.Impl
