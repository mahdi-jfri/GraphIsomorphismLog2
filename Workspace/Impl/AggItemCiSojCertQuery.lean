module

public import Workspace.Impl.AggItemCiSojRectLib
public import Workspace.Impl.AggItemCiSojRectNumbers
public import Workspace.Impl.AggItemCiSojCtxShape

@[expose] public section

/-! # Every physical-query program precondition at the certified rectangle call -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val encPerm)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- Construct the actual first request from a paid certified representation.
All physical-query palette, degree, canonical-parent-field and numeric input
premises are proved here from the supplied context and object contracts. -/
theorem itcs_cert_query_call (I : Iface) {Pg : Program} {Funs₀ : Funs} {A : itcsRectIdx}
    (hA : itcsRectOk Pg A) {e : Ω ≃ Fin k} {c : C → ℕ} {sv₀ lv : Val}
    (hcall : AsCall I Pg Funs₀ e c S sv₀ lv L) (K : ItSCtx k S L) (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (b : Fin (P₀.κ+1) → Fin L.q) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB)
    (hg : itcsRectGuard X Y y₀ (X.idx hx) cert)
    (hc : RectConds P₀ S L.toGiantLabels (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))
    (rep : RectRep P₀ S L.toGiantLabels (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L.toGiantLabels rep.H hs)
    (hlen : hs.length≤ k^2)
    (wr : (rcRepVal e rep hs).wt≤ Br (rcRepIn K.sv L.q K.ps (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)).wt)
    (sv : List Val) (hier : Val) (hsv : K.sv=.list sv)
    (hsvk : sv[0]?=some (.nat k))
    (hsvd : sv[2]?=some (encFun fun i => if e.symm i∈S.dom then 1 else 0))
    (hsvh : sv[5]?=some hier) (hsvN : sv[9]?=some (.nat S.N)) (hhier : HierValC e hier S.hier) :
    let QF := itcsFrameOf hc rep X Y (certVals X (X.idx hx) cert).2.2
      (itcsCertAlign X Y y₀ (X.idx hx) cert hg) hs hhs hlen hier hhier
    FunDet Pg A.query.ask (.list [K.sv,.nat L.q,rcCertIn X x₀,rcCertIn Y y₀,
      .nat (certVals X (X.idx hx) cert).2.2,encPerm QF.a₀.val,
      .list ((itciMs (itcsFixColor QF.W) (itciOt (itcsFixColor QF.W))).map encPerm),
      rcRepVal e rep hs,encPerm (1:Perm (Fin L.q)),encFun (itcsSide QF.W QF.R)])
      (itcsAskV (QF.query 1) QF.payload (.list QF.pending))
      ((itcsGrow pf Bc Br hBc hBr)^[65] (I.inW .giant S+100)) ∧
      QF.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (I.inW .giant S+100) := by
  let W₀ := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have up {a : ℕ} (h : a≤ G (W₀+100)) : a≤ G^[3] (W₀+100) :=
    itcs_budget_lift pf Bc Br hBc hBr W₀ (i:=1) (by decide) h
  have hsize := itS_size I Pg Funs₀ hcall
  obtain ⟨hk,_,_⟩ := itcs_parent_sizes I hcall
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have hB : 2*L.q^P₀.κ≤2*(2*W₀+3)^64 := Nat.mul_le_mul_left 2 hsize.2.2.1
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W₀ k L.q (2*L.q^P₀.κ) hk hq hB
  have wo := itcs_parent_obj_stage I hcall ho pf Bc Br hBc hBr
  obtain ⟨_,_,_,hX,hY⟩ := ho
  have palette := itcs_cert_palette X x₀ hX (X.idx hx) cert
  have objB := itcs_obj_bound_stage pf Bc Br hBc hBr W₀ L.q (2*L.q^P₀.κ) hq hB
  have qnat1 := itcs_nat_parent_weight hq
  have qnat := up (qnat1.trans (itcs_parent_small_stage pf Bc Br hBc hBr W₀ 100 3 2 (by decide) (by decide) (by decide)))
  have wx : (rcCertIn X x₀).wt≤ G^[3] (W₀+100) := up
    ((st_wt_mem (v:=rcCertIn X x₀) (vs:=[.nat 2,rcCertIn X x₀])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wo.1)
  have wy : (rcCertIn Y y₀).wt≤ G^[3] (W₀+100) := up
    ((st_wt_mem (v:=rcCertIn Y y₀) (vs:=[.nat 2,rcCertIn Y y₀])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wo.2)
  have wv := up ((itcs_palette_scalar_weight (q:=L.q) palette.2.2).trans objB)
  have wp := up ((itcs_perm_parent_weight hq).trans
    (itcs_parent_small_stage pf Bc Br hBc hBr W₀ 16 2 2 (by decide) (by decide) (by decide)))
  have wk : k≤ G^[3] (W₀+100) :=
    (hk.trans (Nat.le_add_right W₀ 100)).trans (itcs_budget_base pf Bc Br hBc hBr W₀ 3)
  have wsv : K.sv.wt≤ G^[3] (W₀+100) :=
    ((itS_svW I Pg Funs₀ hcall hK).trans (Nat.le_add_right W₀ 100)).trans
      (itcs_budget_base pf Bc Br hBc hBr W₀ 3)
  have wrep := wr.trans (itcs_rep_cost_stage I hcall hK pf Bc Br hBc hBr _ _)
  have hq2 : 2≤ L.q := (by decide : 2≤ P₀.q₀).trans hcall.q₀.le
  have sideCall := itcs_cert_side_table hA.sides hA.sideB X x₀ hx hX hq2 cert
  have wside := up ((itcs_det_weight sideCall).trans leaf.side)
  have fixCall := itcs_side_fix_prog hA.part hA.fix hA.query.rng hA.fixMap hA.fixB hA.fixGen
    (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)
  have wfix := up ((itcs_det_weight fixCall).trans leaf.fix)
  have wans := up ((itcs_answer_cost_mono hk).trans
    (itcs_parent_profile pf Bc Br hBc hBr W₀ (f:=ansW)
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[20]?=some ansW from rfl))))
  have hpM : pM k L.q hs≤ k+L.q+k^2+2 := Nat.add_le_add_right (Nat.add_le_add_left hlen _) 2
  have phys := up ((itcs_phys_cost_mono hpM).trans leaf.phys)
  have lc := up ((itcs_swap_lc_cost_mono hpM).trans leaf.lc)
  have kr := up ((Nat.mul_le_mul_left 7000 (Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 3)).trans
    (itcs_parent_small_stage pf Bc Br hBc hBr W₀ 7000 1 3 (by decide) (by decide) (by decide)))
  dsimp only
  rw [hsv]
  exact itcs_query_ask_global hA.query pf Bc Br hBc hBr W₀ hc rep X Y x₀ y₀ hX hY _ palette.2.2
    (itcsCertAlign X Y y₀ (X.idx hx) cert hg) hs hhs hlen sv hier
    (encFun (itcsSide (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))) hhier hsvk hsvd hsvh hsvN
    (by simpa only [hsv] using wsv) wx wy wv qnat wp wk wrep wside wfix wans phys lc kr
    (up leaf.dom) (up leaf.compose) (up leaf.range) (up leaf.pull)

end GI.Impl
