import Workspace.Impl.AggItemCiSojRectRun
import Workspace.Impl.AggItemCiSojInputBudget

/-! # The full certified rectangle controller's common global cost -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The complete five-field certificate encoding fits stage two. Its first
three values use the object palette bound; its witnesses use the label degree. -/
theorem itcs_cert_value_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (X : PairCfg L.q) (x₀ : Fin L.q) (hx : x₀∈X.fiber)
    (hX : itCfColsLe (.pair X x₀) (2*L.q^P₀.κ))
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) :
    (rcCertVal X (X.idx hx) cert).wt≤(itcsGrow pf Bc Br hBc hBr)^[2] (I.inW .giant S+100) := by
  let W₀ := I.inW .giant S
  have size := itS_size I Pg F hc
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have objB := itcs_obj_bound_stage pf Bc Br hBc hBr W₀ L.q (2*L.q^P₀.κ) hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have palette := itcs_cert_palette X x₀ hX (X.idx hx) cert
  have raw {v : ℕ} (hv : v≤2*L.q^P₀.κ) : (Val.nat v).wt≤ itcsGrow pf Bc Br hBc hBr (W₀+100) :=
    (itcs_palette_scalar_weight (q:=L.q) hv).trans objB
  have point (a : Fin L.q) : (Val.nat a).wt≤ itcsGrow pf Bc Br hBc hBr (W₀+100) :=
    (itcs_nat_parent_weight (a.isLt.le.trans hq)).trans
      (itcs_parent_small_stage pf Bc Br hBc hBr W₀ 100 3 2 (by decide) (by decide) (by decide))
  exact itcs_budget_linear pf Bc Br hBc hBr W₀ 1 (itcs_input_five _ _ _ _ _
    (raw palette.1) (raw palette.2.1) (raw palette.2.2) (point _) (point _))

/-- The exact controller input, including the complete source item input,
fiber, balanced source table and certificate, fits stage three. -/
theorem itcs_rect_input_stage (I : Iface) {Pg : Program} {F : Funs} {A : itcsRectIdx}
    (hA : itcsRectOk Pg A) {e : Ω ≃ Fin k} {c : C → ℕ} {sv lv : Val}
    (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) :
    (Val.list [.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []],
      itcqFV X,encFun (itcsBal X x₀),rcCertVal X (X.idx hx) cert]).wt≤
      (itcsGrow pf Bc Br hBc hBr)^[3] (I.inW .giant S+100) := by
  let W₀ := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have up {a : ℕ} (h : a≤ G (W₀+100)) : a≤ G^[2] (W₀+100) :=
    itcs_budget_lift pf Bc Br hBc hBr W₀ (i:=1) (by decide) h
  have size := itS_size I Pg F hc
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have hk := (itcs_parent_sizes I hc).1
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W₀ k L.q (2*L.q^P₀.κ) hk hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have wi := itcs_start_input_stage I hc hK ho pf Bc Br hBc hBr
  have cols := ho
  obtain ⟨_,_,_,colX,_⟩ := cols
  have cv := itcs_cert_value_stage I hc pf Bc Br hBc hBr X x₀ hx colX cert
  have bp := itcs_bal_table hA.bal hA.balB hA.fiberB X x₀ colX
  have wb := up ((itcs_det_weight bp).trans leaf.balance)
  have hf0 := itcs_fv_weight X
  have hfp := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2)
  have he : 5*(2*W₀+3+1)^2=20*(W₀+2)^2 := by ring
  have wf := up ((hf0.trans (hfp.trans_eq he)).trans
    (itcs_parent_small_stage pf Bc Br hBc hBr W₀ 20 2 2 (by decide) (by decide) (by decide)))
  exact itcs_budget_linear pf Bc Br hBc hBr W₀ 2 (itcs_data_four _ _ _ _ wi wf wb cv)

/-- All leaf costs fit stage one and the cited representation call fits stage
three. After asking the initial query at stage 65, the full controller costs at
most stage 66. -/
theorem itcs_rect_own_stage (I : Iface) {Pg : Program} {F : Funs} {A : itcsRectIdx}
    (hA : itcsRectOk Pg A) {e : Ω ≃ Fin k} {c : C → ℕ} {sv lv : Val}
    (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    {b : Fin (P₀.κ+1) → Fin L.q} {X Y : PairCfg L.q} {x₀ y₀ : Fin L.q}
    (ho : ItCfObjOf K b (.pair X x₀) (.pair Y y₀)) (hx : x₀∈X.fiber)
    (cert : RectangleCertificate X.coloring false (X.idx hx) etaB) :
    let inp := Val.list [.list [K.v,stTv b,itCfOutV (.pair X x₀),itCfOutV (.pair Y y₀),.list []],
      itcqFV X,encFun (itcsBal X x₀),rcCertVal X (X.idx hx) cert]
    itcsRectOwnC (I.inW .giant S) L.q (2*L.q^P₀.κ) inp.wt
      (Br (rcRepIn K.sv L.q K.ps (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert)).wt)
      ((itcsGrow pf Bc Br hBc hBr)^[65] (I.inW .giant S+100)) ≤
      (itcsGrow pf Bc Br hBc hBr)^[66] (I.inW .giant S+100) := by
  let W₀ := I.inW .giant S
  let G := itcsGrow pf Bc Br hBc hBr
  have size := itS_size I Pg F hc
  have hq : L.q≤2*W₀+3 := by dsimp only [W₀]; omega
  have leaf := itcs_leaf_bounds pf Bc Br hBc hBr W₀ k L.q (2*L.q^P₀.κ) (itcs_parent_sizes I hc).1 hq
    (Nat.mul_le_mul_left 2 size.2.2.1)
  have up {a : ℕ} (h : a≤ G (W₀+100)) : a≤ G^[65] (W₀+100) :=
    itcs_budget_lift pf Bc Br hBc hBr W₀ (i:=1) (by decide) h
  have wi := itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 3≤65)
    (itcs_rect_input_stage I hA hc hK pf Bc Br hBc hBr ho hx cert)
  have wr := itcs_budget_lift pf Bc Br hBc hBr W₀ (by decide : 3≤65)
    (itcs_rep_cost_stage I hc hK pf Bc Br hBc hBr (rectW X (X.idx hx) cert) (rectR X (X.idx hx) cert))
  exact itcs_budget_linear pf Bc Br hBc hBr W₀ 65
    (itcs_rect_cost_scalar wi (up leaf.range) (up leaf.balance) (up leaf.side) (up leaf.guard)
      (up leaf.align) (up leaf.fix) (up leaf.mark) (up leaf.mark) wr (le_refl _))

end GI.Impl
