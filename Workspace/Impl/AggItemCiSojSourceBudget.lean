module

public import Workspace.Impl.AggItemCiSojSourceLib
public import Workspace.Impl.AggItemCiSojInputBudget

@[expose] public section

/-! # The source-dispatch scan, certificate and wrapper costs -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

private theorem itcs_pc_input_scalar (table fiber n j : Val) {M : ℕ}
    (ht : table.wt≤ M) (hf : fiber.wt≤ M) (hn : n.wt≤ M) (hj : j.wt≤ M) :
    (Val.list [.list [table,fiber,n],j]).wt≤10^9*(M+100) := by
  have h := wt_list3_le table fiber n
  have hh := wt_list2_le (.list [table,fiber,n]) j
  omega

private theorem itcs_pc_scalar {W n : ℕ} (h : W≤ n) : 50*(W+1)≤10^9*(n+100) := by omega

/-- The actual scan-index/color lookup call has all structural arguments paid
for by the source object and the actual front result. Its cost fits stage three. -/
theorem itcs_pc_cost_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L}
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) {front : ℕ}
    (hfront : FunDet Pg front (rcCertIn X x₀) (.list [itcqFV X,.nat (itcsImpScan X)])
      (itcsFrontC L.q (2*L.q^P₀.κ))) :
    50*((Val.list [.list [rcColVal X,itcqFV X,.nat X.fiber.card],.nat (itcsImpScan X)]).wt+1)≤
      (itcsGrow pf Bc Br hBc hBr)^[3] (I.inW .giant S+100) := by
  let W := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have size := itS_size I Pg F hc
  have hq : L.q≤2*W+3 := by dsimp only [W]; omega
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W k L.q (2*L.q^P₀.κ) (itcs_parent_sizes I hc).1 hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have wo := (itcs_parent_obj_stage I hc ho pf Bc Br hBc hBr).1
  have wx : (rcCertIn X x₀).wt≤ G (W+100) :=
    (st_wt_mem (v:=rcCertIn X x₀) (vs:=[.nat 2,rcCertIn X x₀])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wo
  have wt : (rcColVal X).wt≤ G (W+100) :=
    (st_wt_mem (v:=rcColVal X) (vs:=[rcColVal X,.nat X.j,.nat x₀]) (List.mem_cons_self ..)).trans wx
  have wfout := (itcs_det_weight hfront).trans leaf.front
  have wf : (itcqFV X).wt≤ G (W+100) :=
    (st_wt_mem (v:=itcqFV X) (vs:=[itcqFV X,.nat (itcsImpScan X)]) (List.mem_cons_self ..)).trans wfout
  have wj : (Val.nat (itcsImpScan X)).wt≤ G (W+100) :=
    (st_wt_mem (v:=.nat (itcsImpScan X)) (vs:=[itcqFV X,.nat (itcsImpScan X)])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wfout
  have hn : X.fiber.card≤ L.q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have wn := (itcs_nat_parent_weight (hn.trans hq)).trans
    (itcs_parent_small_stage pf Bc Br hBc hBr W 100 3 2 (by decide) (by decide) (by decide))
  have wi := itcs_budget_linear pf Bc Br hBc hBr W 1 (itcs_pc_input_scalar _ _ _ _ wt wf wn wj)
  exact itcs_budget_linear pf Bc Br hBc hBr W 2 (itcs_pc_scalar wi)

/-- The source wrapper's actual callee budgets. -/
def itcsSourceOwnC (W q B input Ccert Cpc Crect : ℕ) : ℕ :=
  itcsStartC input (itcsFrontC q B) Cpc (itcsImpPartC q B) (7000*(q+1)^3)
    (itcsBalTC q B) (itcsBTC q B) (itcsBalPartC q B) Ccert Crect

/-- The complete source dispatch, including the full rectangle branch at stage
66, fits stage 67 of the same polynomial bound. -/
theorem itcs_source_own_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) :
    itcsSourceOwnC (I.inW .giant S) L.q (2*L.q^P₀.κ)
      (Val.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []]).wt
      (Bc (rcCertIn X x₀).wt) ((itcsGrow pf Bc Br hBc hBr)^[3] (I.inW .giant S+100))
      ((itcsGrow pf Bc Br hBc hBr)^[66] (I.inW .giant S+100)) ≤
      (itcsGrow pf Bc Br hBc hBr)^[67] (I.inW .giant S+100) := by
  let W := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have size := itS_size I Pg F hc
  have hq : L.q≤2*W+3 := by dsimp only [W]; omega
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W k L.q (2*L.q^P₀.κ) (itcs_parent_sizes I hc).1 hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have up {a : ℕ} (h : a≤ G (W+100)) : a≤ G^[66] (W+100) :=
    itcs_budget_lift pf Bc Br hBc hBr W (i:=1) (by decide) h
  have wi := itcs_budget_lift pf Bc Br hBc hBr W (by decide : 2≤66)
    (itcs_start_input_stage I hc hK ho pf Bc Br hBc hBr)
  have wc := itcs_budget_lift pf Bc Br hBc hBr W (by decide : 2≤66)
    (itcs_cert_cost_stage I hc ho pf Bc Br hBc hBr)
  have wpc : G^[3] (W+100)≤ G^[66] (W+100) :=
    itcs_budget_lift pf Bc Br hBc hBr W (by decide : 3≤66) (le_refl _)
  have own := itcs_start_cost_bound wi (up leaf.front) wpc (up leaf.imppart) (up leaf.range)
    (up leaf.balance) (up leaf.test) (up leaf.balpart) wc (le_refl _)
  exact own.trans (itcs_budget_local pf Bc Br hBc hBr (f:=itcsWrapperC)
    (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[18]?=some itcsWrapperC from rfl)) W 66 (le_refl _))

end GI.Impl
