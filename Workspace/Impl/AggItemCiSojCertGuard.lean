module

public import Workspace.Impl.AggItemCiSojRectLib
public import Workspace.Impl.AggItemCiSojRectNumbers

@[expose] public section

/-! # The literal rectangle guard and fixed alignment at the actual program calls -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val encPerm)
open Classical

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The size-only callback computes exactly the model's full rectangle guard:
source size/disjointness and target disjointness have already been proved. -/
theorem itcs_cert_guard_prog {Pg : Program} {A : itcsRectIdx} (hA : itcsRectOk Pg A)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB)
    (hX : X.Good deltaB) (hq : 16≤ L.q) :
    FunDet Pg A.guard (.list [encFun (itcsSide (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)),
      encFun (itcsSides Y y₀ (certVals X (X.idx hx) cert).1 (certVals X (X.idx hx) cert).2.1)])
      (.nat (if itcsRectGuard X Y y₀ (X.idx hx) cert then 1 else 0)) (itcsGuardC L.q) := by
  have hd : Disjoint (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert) :=
    Finset.disjoint_map _ |>.2 cert.disjoint
  have ht := itcs_target_disjoint Y y₀ (itcs_cert_colors X (X.idx hx) cert)
  have hprog := itcs_guard_prog hA.guard hA.count _ _ _ _ hd ht
  have hi := itcs_guard_iff X Y y₀ (X.idx hx) cert hX hq
  change itcsRectGuard X Y y₀ (X.idx hx) cert ↔ _ at hi
  have he : boolVal (decide ((rectW X (X.idx hx) cert).card=
      (Y.fiber.filter fun a => Y.col y₀ a=(certVals X (X.idx hx) cert).1).card ∧
      (rectR X (X.idx hx) cert).card=
      (Y.fiber.filter fun a => Y.col y₀ a=(certVals X (X.idx hx) cert).2.1).card)) =
      Val.nat (if itcsRectGuard X Y y₀ (X.idx hx) cert then 1 else 0) := by
    by_cases hg : itcsRectGuard X Y y₀ (X.idx hx) cert
    · simp [boolVal,hg,hi.mp hg]
    · have hn := mt hi.mpr hg
      simp [boolVal,hg,hn]
  simpa only [he,itcsSides] using hprog

/-- When the literal guard passes, the partition alignment program returns the
exact even alignment fixed in the model's `itcsChoices`. -/
theorem itcs_cert_align_prog {Pg : Program} {A : itcsRectIdx} (hA : itcsRectOk Pg A)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB)
    (hg : itcsRectGuard X Y y₀ (X.idx hx) cert) {W₀ : ℕ} (hq : L.q≤2*W₀+3) :
    FunDet Pg A.align (.list [encFun (itcsSide (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)),
      encFun (itcsSides Y y₀ (certVals X (X.idx hx) cert).1 (certVals X (X.idx hx) cert).2.1)])
      (encPerm (itcsCertAlign X Y y₀ (X.idx hx) cert hg).val) (itcsAlignC (100*(2*W₀+4)^2)) := by
  have counts := itcs_side_counts hg.2.2.2.1 hg.2.2.2.2 hg.1 hg.2.1 hg.2.2.1
  exact itcs_align_prog hA.part hA.align counts hg.2.2.1
    (itcs_side_align_weight _ _ hq) (itcs_side_align_weight _ _ hq)

end GI.Impl
