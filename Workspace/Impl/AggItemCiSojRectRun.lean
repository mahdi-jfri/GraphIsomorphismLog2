module

public import Workspace.Impl.AggItemCiSojCertQuery
public import Workspace.Impl.AggItemCiSojCertGuard
public import Workspace.Impl.AggItemCiSojCertPost

@[expose] public section

/-! # The actual certified rectangle controller satisfies the full item postcondition -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val encPerm encKColoring)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The actual leaf and cited-call costs used by the rectangle controller. -/
def itcsRectOwnC (W q B input Cp Cask : ℕ) : ℕ :=
  itcsRectPrepC input (7000*(q+1)^3) (itcsBalTC q B) (itcsSideC q B) (itcsGuardC q)
    (itcsAlignC (100*(2*W+4)^2)) (itcsFixProgC q) (itcsMarkC q) (itcsMarkC q) Cp Cask

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- The representation and query branches use exactly the certificate,
alignment, implication and representation functions fixed by init. The literal
guard is checked before any of the guarded calls. -/
theorem itcs_rect_run (I : Iface) {Pg : Program} {Funs₀ : Funs} {A : itcsRectIdx}
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
      cost≤ itcsRectOwnC (I.inW .giant S) L.q (2*L.q^P₀.κ) inp.wt
        (Br (rcRepIn K.sv L.q K.ps (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)).wt)
        ((itcsGrow pf Bc Br hBc hBr)^[65] (I.inW .giant S+100)) := by
  let W₀ := I.inW .giant S
  let W := rectW X (X.idx hx) cert
  let R := rectR X (X.idx hx) cert
  let side := encFun (itcsSide W R)
  let target := encFun (itcsSides Y y₀ (certVals X (X.idx hx) cert).1 (certVals X (X.idx hx) cert).2.1)
  let guard := itcsRectGuard X Y y₀ (X.idx hx) cert
  let g := if guard then 1 else 0
  let av : Val := if hg : guard then encPerm (itcsCertAlign X Y y₀ (X.idx hx) cert hg).val else .list []
  let fv := Val.list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm)
  let P : Val → Prop := ItCfIPost (itcsRel I Pg A.rep Br cf pf Bc hBc hBr) e c S L K b
    (.pair X x₀) (.pair Y y₀) E (itcsSb e X Y x₀ y₀)
    (itcsXs pf Bc Br hBc hBr W₀) (itcsXs pf Bc Br hBc hBr W₀)
  have hq16 : 16≤ L.q := (by decide : 16≤ P₀.q₀).trans hcall.q₀.le
  have hq2 : 2≤ L.q := (by decide : 2≤16).trans hq16
  have hq1 : 1≤ L.q := (by decide : 1≤2).trans hq2
  have hsize := itS_size I Pg Funs₀ hcall
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have hc : RectConds P₀ S L.toGiantLabels W R :=
    itcs_rect_conds X (X.idx hx) cert hlarge (itcs_cert_three X (X.idx hx) cert hX hq16)
  have hd : Disjoint W R := Finset.disjoint_map _ |>.2 cert.disjoint
  have goodg (hg : g≠0) : guard := by
    by_contra hn
    simp only [g,if_neg hn] at hg
    exact hg rfl
  have badg (hg : g=0) : ¬guard := by
    intro hh
    simp only [g,if_pos hh] at hg
    exact Nat.one_ne_zero hg
  have cols := ho
  obtain ⟨_,_,_,colX,colY⟩ := cols
  have palette := itcs_cert_palette X x₀ colX (X.idx hx) cert
  have rangeCall := range_det hA.query.rng L.q
  have balCall := itcs_bal_table hA.bal hA.balB hA.fiberB Y y₀ colY
  have sourceCall := itcs_cert_side_table hA.sides hA.sideB X x₀ hx colX hq2 cert
  have targetCall := itcs_side_table hA.sides hA.sideB Y y₀ _ _ colY palette.1 palette.2.1 hq2
  have guardCall := itcs_cert_guard_prog hA X Y x₀ y₀ hx cert hX hq16
  have alignCall (hg : g≠0) : FunDet Pg A.align (.list [side,target]) av (itcsAlignC (100*(2*W₀+4)^2)) := by
    simpa only [av,dif_pos (goodg hg)] using itcs_cert_align_prog hA X Y x₀ y₀ hx cert (goodg hg) hq
  have fixCall := itcs_side_fix_prog hA.part hA.fix hA.query.rng hA.fixMap hA.fixB hA.fixGen W R
  have markWCall := itcs_side_marker_left hA.markW hA.markWB W R hq1
  have markRCall := itcs_side_marker_right hA.markR hA.markRB W R hd hq1
  let RR : Val → Prop := fun rv => ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
    rv=rcRepVal e (rf W R hc) hs ∧ PairGens e L.toGiantLabels (rf W R hc).H hs ∧ hs.length≤ k^2 ∧
      rv.wt≤ Br (rcRepIn K.sv L.q K.ps W R).wt
  have repCall (hg : g≠0) : FunAll Pg A.rep (rcRepIn K.sv L.q K.ps W R)
      (fun rv cost => RR rv ∧ cost≤ Br (rcRepIn K.sv L.q K.ps W R).wt) :=
    (hRep W R hc).mono fun rv cost ⟨hs,he,hg,hl,hc,hw⟩ => ⟨⟨hs,he,hg,hl,hw⟩,hc⟩
  obtain ⟨sv,hier,hsv,hsvk,hsvd,hsvh,hsvN,hhier⟩ := itcs_ctx_shape hK
  have askCall (rv : Val) (hg : g≠0) (hrr : RR rv) :
      FunAll Pg A.query.ask (.list [K.sv,.nat L.q,rcCertIn X x₀,rcCertIn Y y₀,
        .nat (certVals X (X.idx hx) cert).2.2,av,fv,rv,natList (List.range L.q),side])
        (fun w cost => P w ∧ cost≤(itcsGrow pf Bc Br hBc hBr)^[65] (W₀+100)) := by
    obtain ⟨hs,he,hhs,hlen,wr⟩ := hrr
    subst rv
    have hg' := goodg hg
    let QF := itcsFrameOf hc (rf W R hc) X Y (certVals X (X.idx hx) cert).2.2
      (itcsCertAlign X Y y₀ (X.idx hx) cert hg') hs hhs hlen hier hhier
    obtain ⟨hask,hcap⟩ := itcs_cert_query_call I hA hcall K hK pf Bc Br hBc hBr b X Y x₀ y₀ ho hx cert hg'
      hc (rf W R hc) hs hhs hlen wr sv hier hsv hsvk hsvd hsvh hsvN hhier
    have post := itcs_cert_enter I pf hBc hBr e c K hK hgood b X Y x₀ y₀ E rf hKeep hE hx hp hb
      hcert cert hcf hg' hc hs hhs hlen hier hhier hcap
    have hask' : FunDet Pg A.query.ask (.list [K.sv,.nat L.q,rcCertIn X x₀,rcCertIn Y y₀,
        .nat (certVals X (X.idx hx) cert).2.2,av,fv,rcRepVal e (rf W R hc) hs,
        natList (List.range L.q),side]) (itcsAskV (QF.query 1) QF.payload (.list QF.pending)) ((itcsGrow pf Bc Br hBc hBr)^[65] (W₀+100)) := by
      simpa only [av,fv,QF,W₀,side,itcsFrameOf,dif_pos hg',it_range_one] using hask
    exact FunAll.mono hask' fun w cost ⟨he,hcost⟩ => by rw [he]; exact ⟨post,hcost⟩
  have skip (hg : g=0) : P (itcsResV (.list [])) :=
    itcs_cert_skip_post I pf hBc hBr e c K b X Y x₀ y₀ E rf hKeep hE hx hp hb hcert cert hcf (badg hg)
  let oi := [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),Val.list []]
  let ki := [K.st,Val.list [encKColoring K.d,encKColoring K.d'],.nat (AggCase.code K.case),
    natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]
  let si := [K.sv,Val.list [.nat k,.nat L.q],Val.list (K.ps.map pairV),Val.list (K.fx.map pairV),
    Val.list (K.fy.map pairV),stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]
  let xc := [rcColVal X,Val.nat X.j,Val.nat x₀]
  let yc := [rcColVal Y,Val.nat Y.j,Val.nat y₀]
  let cv := [Val.nat (certVals X (X.idx hx) cert).1,Val.nat (certVals X (X.idx hx) cert).2.1,
    Val.nat (certVals X (X.idx hx) cert).2.2,Val.nat (X.emb rfl cert.leftPoint.val),Val.nat (X.emb rfl cert.rightPoint.val)]
  exact itcs_rect_prep_prog hA.body oi ki si [.nat k,.nat L.q] [.nat 2,.list xc] [.nat 2,.list yc]
    xc yc cv (itcqFV X) (encFun (itcsBal X x₀)) K.sv (.nat L.q) (.list (K.ps.map pairV))
    (.nat (certVals X (X.idx hx) cert).1) (.nat (certVals X (X.idx hx) cert).2.1) (.nat (certVals X (X.idx hx) cert).2.2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (natList (List.range L.q)) (encFun (itcsBal Y y₀)) side target av fv (rcSetVal W) (rcSetVal R) g RR P
    rangeCall balCall sourceCall targetCall guardCall alignCall (fun _ => fixCall) (fun _ => markWCall)
    (fun _ => markRCall) repCall askCall skip

end GI.Impl
