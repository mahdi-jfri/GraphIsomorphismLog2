module

public import Workspace.Impl.AggItemCiSojBudgetL
public import Workspace.Impl.AggItemCiSojInit

@[expose] public section

/-! # The global item budget discharges initialization and bounded object inputs -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The parent-call size bounds place the bounded pair objects inside the common
polynomial item budget. -/
theorem itcs_xs_obj_bound (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    itCfObjB L.q (2*L.q^P₀.κ) ≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) := by
  let W := I.inW .giant S
  have hsize := itS_size I Pg F hc
  have hq : L.q ≤ 2*W+3 := by dsimp only [W]; omega
  have hp : L.q^P₀.κ ≤ (2*W+3)^64 := hsize.2.2.1
  have hb : itCfObjB L.q (2*L.q^P₀.κ) ≤ itCfObjB (2*W+3) (2*(2*W+3)^64) := by
    unfold itCfObjB
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 20
      (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 5)
  have hs := itcs_budget_stage pf Bc Br hBc hBr
    (f:=fun W => itCfObjB (2*W+3) (2*(2*W+3)^64))
    (by simp only [itcsCostFns,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])
    W (i:=0) (a:=W) (by decide) (Nat.le_add_right W 100)
  exact hb.trans hs

/-- The `objW` field follows from c23's strengthened object predicate and the
proved global budget. No extra object-weight hypothesis remains. -/
theorem itcs_xs_objW (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) (K : ItSCtx k S L)
    (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    ∀ b oX oY, ItCfObjOf K b oX oY →
      (∀ X x₀, oX = .pair X x₀ → (itCfOutV oX).wt ≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S)) ∧
      (∀ Y y₀, oY = .pair Y y₀ → (itCfOutV oY).wt ≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S)) :=
  itcs_objW (itcs_xs_obj_bound I hc pf Bc Br hBc hBr)

/-- The kept value's constant weight fits the same global polynomial budget. -/
theorem itcs_keep_weight_xs {Pg : Program} {fr : ℕ} {Br : ℕ → ℕ} {cf : RcCertFn}
    {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L} {w : Val}
    {E : Set (ItCfCh S L.toGiantLabels)} (h : itcsKeep Pg fr Br cf e c K w E)
    (pf : Prim) (Bc : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W)
    (hBr : PBU fun _ W _ => Br W) (W : ℕ) : w.wt ≤ itcsXs pf Bc Br hBc hBr W := by
  have hw := itcs_keep_weight h
  have hb := itcs_budget_input pf Bc Br hBc hBr W
  omega

/-- The actual init satisfies its global cost bound. The representation contract
is called with every context precondition supplied by `K.OK` and `AsCall.inj`. -/
theorem itcs_init_xs (I : Iface) {Pg : Program} {F : Funs} {fi fr : ℕ}
    {e : Ω ≃ Fin k} {c : C → ℕ} {sv lv : Val}
    (hc : AsCall I Pg F e c S sv lv L) (K : ItSCtx k S L) (hK : K.OK e c)
    (cf : RcCertFn) (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (hfi : Pg.funs[fi]? = some Expr.nil) (hr : RcRepSpec Pg fr Br) :
    FunAll Pg fi K.v fun w cost => ∃ E, itcsKeep Pg fr Br cf e c K w E ∧
      cost ≤ itcsXs pf Bc Br hBc hBr (I.inW .giant S) := by
  have hb := itcs_budget_input pf Bc Br hBc hBr (I.inW .giant S)
  exact (itcs_init cf hfi hr e c K hc.inj hK).mono fun w cost ⟨E,hE,hcost⟩ =>
    ⟨E,hE,hcost.trans (by omega)⟩

end GI.Impl
