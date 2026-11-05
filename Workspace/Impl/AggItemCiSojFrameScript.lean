module

public import Workspace.Impl.AggItemCiSojFrameBuild
public import Workspace.Impl.AggItemCiSojRectScript

@[expose] public section

/-! # The fixed start choices give the retained frame's exact model script -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- The alignment stored by the program, including its evenness proof. -/
noncomputable def itcsCertAlign (X Y : PairCfg L.q) (y₀ : Fin L.q) (i₀ : Fin X.fiber.card)
    (cert : RectangleCertificate X.coloring false i₀ etaB) (hg : itcsRectGuard X Y y₀ i₀ cert) :
    alternatingGroup (Fin L.q) :=
  ⟨itcsAlign (rectW X i₀ cert) (rectR X i₀ cert)
    (Y.fiber.filter fun a => Y.col y₀ a=(certVals X i₀ cert).1)
    (Y.fiber.filter fun a => Y.col y₀ a=(certVals X i₀ cert).2.1),itcs_align_sign hg.2.2.1⟩

/-- All choices in a successful rectangle branch are the fixed certificate,
fixed even alignment and fixed representation functions stored by init. -/
theorem itcs_frame_script (cf : RcCertFn)
    (rf : ∀ W R : Finset (Fin L.q), RectConds P₀ S L W R → RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (hx : x₀∈X.fiber)
    (hp : PrimitiveColorCuts X.coloring false)
    (hb : ¬ ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hcert : Nonempty (RectangleCertificate X.coloring false (X.idx hx) etaB))
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB)
    (hcf : cf X (X.idx hx) hcert=cert) (hg : itcsRectGuard X Y y₀ (X.idx hx) cert)
    (hc : RectConds P₀ S L (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))
    (hs : List (Perm (Fin k) × Perm (Fin L.q)))
    (hhs : PairGens e L (rf _ _ hc).H hs) (hlen : hs.length≤ k^2)
    (hier : Val) (hhier : HierValC e hier S.hier) :
    let F := itcsFrameOf hc (rf _ _ hc) X Y (certVals X (X.idx hx) cert).2.2
      (itcsCertAlign X Y y₀ (X.idx hx) cert hg) hs hhs hlen hier hhier
    itcsSb e X Y x₀ y₀ (itcsChoices cf,rf) =
      itcsQuerySeq F.rep F.M F.N F.a₀ (itcsTwists F.rep) [] := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  dsimp only
  change (sojItem (RectOracle.ofReps rf) (itcsChoices cf) X Y x₀ y₀).script = _
  rw [itcs_cert_script _ _ X Y x₀ y₀ hx hp hb hcert]
  simp only [itcs_choices_cert]
  rw [hcf,itcs_rect_query_script _ _ X Y y₀ (X.idx hx) cert hg]
  rw [itcs_source_matrix]
  exact itcs_rect_oracle_script rf _ _ hc _ _ _

end GI.Impl
