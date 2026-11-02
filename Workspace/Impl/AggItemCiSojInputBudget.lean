import Workspace.Impl.AggItemCiSojRepBudget

/-! # The actual source item and certificate input budgets -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- Linear scalar constructor bound for five paid input fields. -/
theorem itcs_input_five (a b c d e : Val) {n : ℕ}
    (ha : a.wt≤ n) (hb : b.wt≤ n) (hc : c.wt≤ n) (hd : d.wt≤ n) (he : e.wt≤ n) :
    (Val.list [a,b,c,d,e]).wt≤10^9*(n+100) := by
  have h := itcs_wt_list5 a b c d e
  omega

/-- The exact five-field source-item input fits the second analysis stage. -/
theorem itcs_start_input_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀))
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    (Val.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []]).wt≤
      (itcsGrow pf Bc Br hBc hBr)^[2] (I.inW .giant S+100) := by
  let W := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  obtain ⟨_,hq,hκ⟩ := itcs_parent_sizes I hc
  have wb0 : (stTv b).wt≤5*(W+3)^2 := it_wt_src b hq hκ
  have wb : (stTv b).wt≤ G (W+100) := wb0.trans
    (itcs_parent_small_stage pf Bc Br hBc hBr W 5 3 2 (by decide) (by decide) (by decide))
  have wk : K.v.wt≤ G (W+100) := itcs_parent_value_stage I hc hK pf Bc Br hBc hBr
  have wo := itcs_parent_obj_stage I hc ho pf Bc Br hBc hBr
  have wn : (Val.list []).wt≤ G (W+100) := by
    have h := itcs_grow_le pf Bc Br hBc hBr (W+100)
    simp only [wt_list_nil]
    exact (show 4≤ W+100 by omega).trans h
  exact itcs_budget_linear pf Bc Br hBc hBr W 1 (itcs_input_five _ _ _ _ _ wk wb wo.1 wo.2 wn)

/-- The certificate function is applied at its actual source-table input. Its
own cost and returned encoding fit the second analysis stage. -/
theorem itcs_cert_cost_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L}
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀))
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    Bc (rcCertIn X x₀).wt≤(itcsGrow pf Bc Br hBc hBr)^[2] (I.inW .giant S+100) := by
  have wo := (itcs_parent_obj_stage I hc ho pf Bc Br hBc hBr).1
  have wi : (rcCertIn X x₀).wt≤ itcsGrow pf Bc Br hBc hBr (I.inW .giant S+100) :=
    (st_wt_mem (v:=rcCertIn X x₀) (vs:=[.nat 2,rcCertIn X x₀])
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wo
  exact itcs_budget_local pf Bc Br hBc hBr (f:=Bc)
    (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[0]?=some Bc from rfl)) _ 1 wi

end GI.Impl
