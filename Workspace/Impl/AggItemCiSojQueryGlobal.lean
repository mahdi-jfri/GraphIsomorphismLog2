import Workspace.Impl.AggItemCiSojQueryProg

/-! # The complete installed query pipeline within the common polynomial budget -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

private theorem itcs_query_linear_le (n : ℕ) : n≤10^9*(n+100) :=
  (Nat.le_add_right n 100).trans (Nat.le_mul_of_pos_left _ (by decide : 0<10^9))

private theorem itcs_query_twolinear_mono {a b : ℕ} (h : a≤ b) :
    10^9*(10^9*(a+100)+100)≤10^9*(10^9*(b+100)+100) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 100)) 100)

/-- The physical group/domain/context constructor, both table pullbacks, and
the request constructor are actual installed programs. Their full composition
has cost at stage 65 and the retained-frame cap at stage 126. -/
theorem itcs_query_ask_global {Pg : Program} {Q : itcsQueryIdx} (hQ : itcsQueryOk Pg Q)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W₀ : ℕ) (hc : RectConds P₀ S L W R) (rep : RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) {B : ℕ}
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B)
    (v : ℕ) (hv : v≤ B) (a : alternatingGroup (Fin L.q))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (hlen : hs.length≤ k^2) (sv : List Val) (hier side : Val) (hhier : HierValC e hier S.hier)
    (hsvk : sv[0]?=some (.nat k))
    (hsvd : sv[2]?=some (encFun fun i => if e.symm i∈S.dom then 1 else 0))
    (hsvh : sv[5]?=some hier) (hsvN : sv[9]?=some (.nat S.N))
    (wsv : (Val.list sv).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wX : (rcCertIn X x₀).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wY : (rcCertIn Y y₀).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wv : (Val.nat v).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wq : (Val.nat L.q).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wp : 4*(L.q+1)^2≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wk : k≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wrep : (rcRepVal e rep hs).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wside : side.wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wfix : (Val.list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm)).wt≤
      (itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (wans : ansW k≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (cg : itcsPhysC (pM k L.q hs)≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (cl : itcsSwapLcC (pM k L.q hs)≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (crk : 7000*(k+1)^3≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (cd : itcsDomC k L.q≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (ccmp : permK*(L.q+1)^3≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (crq : 7000*(L.q+1)^3≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100))
    (cpull : itcsPullC k L.q B≤(itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100)) :
    let F := itcsFrameOf hc rep X Y v a hs hhs hlen hier hhier
    FunDet Pg Q.ask (.list [.list sv,.nat L.q,rcCertIn X x₀,rcCertIn Y y₀,.nat v,encPerm a.val,
      .list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm),
      rcRepVal e rep hs,encPerm (1:Perm (Fin L.q)),side])
      (itcsAskV (F.query 1) F.payload (.list F.pending))
      ((itcsGrow pf Bc Br hBc hBr)^[65] (W₀+100)) ∧
      F.weight≤(itcsGrow pf Bc Br hBc hBr)^[126] (W₀+100) := by
  let F := itcsFrameOf hc rep X Y v a hs hhs hlen hier hhier
  let n := (itcsGrow pf Bc Br hBc hBr)^[3] (W₀+100)
  let D := 10^9*(10^9*(n+100)+100)
  let Cq := 10^9*(10^9*(D+100)+100)
  have nd : n≤ D := (itcs_query_linear_le n).trans (itcs_query_linear_le (10^9*(n+100)))
  have dataCall := itcs_physical_frame_bounded hQ.data hQ.gp hQ.fm hQ.fst hQ.group hQ.lc hQ.sw
    hQ.hv hQ.rng hQ.gr hQ.en hQ.fsm hQ.dom hQ.db F sv hsvk hsvd wsv wq wrep cg cl crk cd
  have wdata : (Val.list [encGroup (hs.map Prod.fst),
      encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),liftLabCtx L.q k (hs.map Prod.swap)]).wt≤ D :=
    itcs_det_weight dataCall
  have wx : (rcColVal X).wt≤ n := (st_wt_mem (v:=rcColVal X)
    (vs:=[rcColVal X,.nat X.j,.nat x₀]) (List.mem_cons_self ..)).trans wX
  have wy : (rcColVal Y).wt≤ n := (st_wt_mem (v:=rcColVal Y)
    (vs:=[rcColVal Y,.nat Y.j,.nat y₀]) (List.mem_cons_self ..)).trans wY
  have queryCall := itcs_colors_frame_bounded hQ.colors hQ.cmp hQ.rng hQ.pull hQ.cb hQ.bit hQ.state
    hc rep X Y x₀ y₀ hX hY v hv a hs hhs hlen sv hier hhier hsvk hsvh hsvN
    (ccmp.trans nd) (crq.trans nd) (cpull.trans nd) (wsv.trans nd) (wx.trans nd) (wy.trans nd)
    (wv.trans nd) (wq.trans nd) (wp.trans nd) (wk.trans nd) (wrep.trans nd) wdata
  have d5 : D≤(itcsGrow pf Bc Br hBc hBr)^[5] (W₀+100) := itcs_budget_twolinear pf Bc Br hBc hBr W₀ 3
  have q7 : Cq≤(itcsGrow pf Bc Br hBc hBr)^[7] (W₀+100) :=
    (itcs_query_twolinear_mono d5).trans (itcs_budget_twolinear pf Bc Br hBc hBr W₀ 5)
  have wa : (encPerm a.val).wt≤ n := (wt_encPerm_le _).trans wp
  have wid : (encPerm (1:Perm (Fin L.q))).wt≤ n := (wt_encPerm_le _).trans wp
  have wi := itcs_list10_scalar (.list sv) (.nat L.q) (rcCertIn X x₀) (rcCertIn Y y₀)
    (.nat v) (encPerm a.val) (.list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm))
    (rcRepVal e rep hs) (encPerm (1:Perm (Fin L.q))) side wsv wq wX wY wv wa wfix wrep wid wside
  have wi4 := itcs_budget_linear pf Bc Br hBc hBr W₀ 3 wi
  exact itcs_ask_global hQ.ask F (.list sv) (.nat v) side (rcColVal X) (rcColVal Y)
    [rcColVal X,.nat X.j,.nat x₀] [rcColVal Y,.nat Y.j,.nat y₀] rfl rfl dataCall queryCall
    pf Bc Br hBc hBr W₀
    (itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 5≤64) d5)
    (itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 7≤64) q7)
    (itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 3≤65) wans)
    (itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 4≤64) wi4)

end GI.Impl
