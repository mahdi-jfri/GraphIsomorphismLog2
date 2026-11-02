import Workspace.Impl.AggItemCiSojBudgetCtx
import Workspace.Impl.AggItemCiSojLeafMono
import Workspace.Impl.AggItemCiSojBudgetStart

/-! # Parent-call bounds for the first-rectangle start -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- Physical and label degrees, and the source-tuple length, are bounded by the
actual parent input weight. -/
theorem itcs_parent_sizes (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) :
    k ≤ I.inW .giant S ∧ L.q ≤ I.inW .giant S+2 ∧ P₀.κ+1 ≤ I.inW .giant S+2 := by
  have hs := itS_size I Pg F hc
  have hk := (StateVal.k_le_wt hc.can.stateVal).trans hs.2.2.2.2.1
  have hq := (GiantLabels.q_le e L.toGiantLabels).trans (Nat.add_le_add_right hk 2)
  exact ⟨hk,hq,hs.2.2.2.2.2.le.trans hq⟩

/-- Every listed parent-size profile is covered by the first analysis stage. -/
theorem itcs_parent_profile (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W : ℕ) {f : ℕ → ℕ} (hf : f∈itcsCostFns pf Bc Br) :
    f W ≤ (itcsGrow pf Bc Br hBc hBr) (W+100) := by
  exact itcs_stage_cost_le pf Bc Br hBc hBr hf (Nat.le_add_right W 100)

/-- The common parent structural profile pays fixed polynomials of degree at
most eight, including range and permutation composition. -/
theorem itcs_parent_small_stage (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W c d a : ℕ) (hc : c ≤ 10^9) (hd : d ≤ 100) (ha : a ≤ 8) :
    c*(W+d)^a ≤ (itcsGrow pf Bc Br hBc hBr) (W+100) :=
  (itcs_wrapper_power W c d a hc hd ha).trans
    (itcs_parent_profile pf Bc Br hBc hBr W
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[18]?=some itcsWrapperC from rfl)))

/-- The supplied context's complete encoded value is covered at stage one. -/
theorem itcs_parent_value_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    K.v.wt ≤ (itcsGrow pf Bc Br hBc hBr) (I.inW .giant S+100) :=
  ((itS_vW I Pg F hc hK).trans (itcs_wrapper_parent _)).trans
    (itcs_parent_profile pf Bc Br hBc hBr _
      (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[18]?=some itcsWrapperC from rfl)))

/-- Both raw pair-object encodings, including their bounded color tables, fit
stage one. This uses the strengthened object predicate. -/
theorem itcs_parent_obj_stage (I : Iface) {Pg : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {sv lv : Val} (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L}
    {b : Fin (P₀.κ+1) → Fin L.q} {oX oY : CfgOut L.q} (ho : ItCfObjOf K b oX oY)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W) :
    (itCfOutV oX).wt ≤ (itcsGrow pf Bc Br hBc hBr) (I.inW .giant S+100) ∧
    (itCfOutV oY).wt ≤ (itcsGrow pf Bc Br hBc hBr) (I.inW .giant S+100) := by
  let W := I.inW .giant S
  have hs := itS_size I Pg F hc
  have hq : L.q ≤ 2*W+3 := by dsimp only [W]; omega
  have hp : L.q^P₀.κ ≤ (2*W+3)^64 := hs.2.2.1
  have hb : itCfObjB L.q (2*L.q^P₀.κ) ≤ itCfObjB (2*W+3) (2*(2*W+3)^64) := by
    unfold itCfObjB
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 20
      (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 5)
  have hstage := itcs_parent_profile pf Bc Br hBc hBr W
    (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[19]?=
      some (fun W => itCfObjB (2*W+3) (2*(2*W+3)^64)) from rfl))
  have hw := itCfObjOf_wt ho
  exact ⟨hw.1.trans (hb.trans hstage),hw.2.trans (hb.trans hstage)⟩

end GI.Impl
