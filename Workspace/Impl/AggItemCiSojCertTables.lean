import Workspace.Impl.AggItemCiSojFrameScript
import Workspace.Impl.AggItemCiSojFP
import Workspace.Impl.AggItemCiSojGC

/-! # Certificate sides and the actual table programs -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val encPerm)
open Classical

variable {q : ℕ}

/-- Reading the two certificate row colors gives the model's original sides. -/
theorem itcs_cert_sides (X : PairCfg q) (x₀ : Fin q) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) :
    itcsSides X x₀ (certVals X (X.idx hx) cert).1 (certVals X (X.idx hx) cert).2.1 =
      itcsSide (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert) := by
  rw [rectW_eq,rectR_eq,X.emb_idx hx]
  rfl

/-- The source side-table call has its palette and minimum-degree premises
supplied by the bounded source object and the parent label degree. -/
theorem itcs_cert_side_table {Pg : Program} {mp f B : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]?=some itcsSideF)
    (X : PairCfg q) (x₀ : Fin q) (hx : x₀∈X.fiber)
    (hcol : itCfColsLe (.pair X x₀) B) (hq : 2≤ q)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) :
    FunDet Pg mp (.list [.list [encFun (itcsBal X x₀),.nat (certVals X (X.idx hx) cert).1,
      .nat (certVals X (X.idx hx) cert).2.1],natList (List.range q)])
      (encFun (itcsSide (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))) (itcsSideC q B) := by
  have hc := itcs_cert_palette X x₀ hcol (X.idx hx) cert
  simpa only [itcs_cert_sides X x₀ hx cert] using
    itcs_side_table hm hf X x₀ _ _ hcol hc.1 hc.2.1 hq

/-- The left-color indicator is exactly the cited representation's set input. -/
theorem itcs_side_marker_left {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]?=some (itcsMarkF 2))
    (W R : Finset (Fin q)) (hq : 1≤ q) :
    FunDet Pg mp (.list [encFun (itcsSide W R),natList (List.range q)]) (rcSetVal W) (itcsMarkC q) := by
  have hl : ∀a,itcsSide W R a≤2 := by intro a; unfold itcsSide; split_ifs <;> omega
  have he : (fun a => (decide (itcsSide W R a=2)).toNat) = (fun a => if a∈W then 1 else 0) := by
    funext a
    simp only [itcs_side_left]
    by_cases ha : a∈W <;> simp [ha]
  simpa only [he,rcSetVal] using itcs_mark_table hm hf (itcsSide W R) hl (by decide) hq

/-- The right-color indicator uses the proved disjointness of the source sides. -/
theorem itcs_side_marker_right {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]?=some (itcsMarkF 1))
    (W R : Finset (Fin q)) (hd : Disjoint W R) (hq : 1≤ q) :
    FunDet Pg mp (.list [encFun (itcsSide W R),natList (List.range q)]) (rcSetVal R) (itcsMarkC q) := by
  have hl : ∀a,itcsSide W R a≤2 := by intro a; unfold itcsSide; split_ifs <;> omega
  have he : (fun a => (decide (itcsSide W R a=1)).toNat) = (fun a => if a∈R then 1 else 0) := by
    funext a
    simp only [itcs_side_right hd]
    by_cases ha : a∈R <;> simp [ha]
  simpa only [he,rcSetVal] using itcs_mark_table hm hf (itcsSide W R) hl (by decide) hq

/-- The pointwise-fixing subgroup is generated from the exact source side table. -/
theorem itcs_side_fix_prog {Pg : Program} {Ii : ItciIdx} {f rng mp mk fg : ℕ}
    (hi : ItciOk Pg Ii) (hf : Pg.funs[f]?=some (itcsFixProgF rng mp fg))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hm : Pg.HasAt mp (mapFuns mp mk))
    (hmarker : Pg.funs[mk]?=some itcsFixMarkF) (hfg : Pg.funs[fg]?=some (itcsFixGenF Ii.f))
    (W R : Finset (Fin q)) :
    FunDet Pg f (encFun (itcsSide W R))
      (.list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm)) (itcsFixProgC q) := by
  have hl : ∀a,itcsSide W R a≤2 := by intro a; unfold itcsSide; split_ifs <;> omega
  simpa only [itcs_fix_from_side] using itcs_fix_prog hi hf hr hm hmarker hfg (itcsSide W R) hl

end GI.Impl
