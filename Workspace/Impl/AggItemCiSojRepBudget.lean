module

public import Workspace.Impl.AggItemCiSojCtxShape
public import Workspace.Impl.AggItemCiSojStartScalar

@[expose] public section

/-! # The cited representation call at its actual encoded input weight -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- Indicator-set bytes are bounded without assuming the set is a domain or a
partition block. -/
theorem itcs_set_parent_weight {q W : ℕ} (U : Finset (Fin q)) (hq : q≤2*W+3) :
    (rcSetVal U).wt≤100*(W+3)^2 := by
  have hu : (rcSetVal U).wt≤7*q+4 := by
    simpa only [rcSetVal,Nat.mul_comm] using
      wt_encFun_le (fun i => if i∈U then 1 else 0) (B:=1) (fun i => by split_ifs <;> omega)
  have hpow : W+3≤(W+3)^2 := Nat.le_self_pow (by decide : 2≠0) (W+3)
  omega

private theorem itcs_rep_five (a b c d e : Val) {n : ℕ}
    (ha : a.wt≤ n) (hb : b.wt≤ n) (hc : c.wt≤ n) (hd : d.wt≤ n) (he : e.wt≤ n) :
    (Val.list [a,b,c,d,e]).wt≤10^9*(n+100) := by
  have h := itcs_wt_list5 a b c d e
  omega

/-- Both set indicators and the stored graph-generator array fit stage one;
the complete five-field representation input therefore fits stage two. -/
theorem itcs_rep_input_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (U V : Finset (Fin L.q)) :
    (rcRepIn K.sv L.q K.ps U V).wt≤(itcsGrow pf Bc Br hBc hBr)^[2] (I.inW .giant S+100) := by
  let W := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have hs := itS_size I Pg F hc
  have hq : L.q≤2*W+3 := by dsimp only [W]; omega
  have wk : K.v.wt≤ G (W+100) := itcs_parent_value_stage I hc hK pf Bc Br hBc hBr
  have wps := (itcs_ctx_ps_weight K).trans wk
  have ws : K.sv.wt≤ G (W+100) :=
    (itS_svW I Pg F hc hK).trans ((Nat.le_add_right W 100).trans (itcs_grow_le pf Bc Br hBc hBr (W+100)))
  have setW (A : Finset (Fin L.q)) : (rcSetVal A).wt≤ G (W+100) :=
    (itcs_set_parent_weight A hq).trans
      (itcs_parent_small_stage pf Bc Br hBc hBr W 100 3 2 (by decide) (by decide) (by decide))
  have wq0 := wt_nat_le L.q
  have wq1 : (Val.nat L.q).wt≤100*(W+3)^2 := by
    have hp : W+3≤(W+3)^2 := Nat.le_self_pow (by decide : 2≠0) (W+3)
    omega
  have wq := wq1.trans (itcs_parent_small_stage pf Bc Br hBc hBr W 100 3 2 (by decide) (by decide) (by decide))
  exact itcs_budget_linear pf Bc Br hBc hBr W 1 (itcs_rep_five _ _ _ _ _ ws wq wps (setW U) (setW V))

/-- The representation cost and every returned generator-array encoding fit
stage three, with no monotonicity assumption on the cited cost function. -/
theorem itcs_rep_cost_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (U V : Finset (Fin L.q)) :
    Br (rcRepIn K.sv L.q K.ps U V).wt≤(itcsGrow pf Bc Br hBc hBr)^[3] (I.inW .giant S+100) :=
  itcs_budget_local pf Bc Br hBc hBr (f:=Br)
    (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[1]?=some Br from rfl)) _ 2
    (itcs_rep_input_stage I hc hK pf Bc Br hBc hBr U V)

end GI.Impl
