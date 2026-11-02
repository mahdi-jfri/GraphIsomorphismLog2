import Workspace.Impl.AggItemCiSojLeafBudget
import Workspace.Impl.AggItemCiSojRepBudget

/-! # Scalar and side-table bounds used at the rectangle's actual calls -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- The bounded object profile also pays for each individual raw color. -/
theorem itcs_palette_scalar_weight {q B v : ℕ} (hv : v≤ B) : (Val.nat v).wt≤ itCfObjB q B := by
  have hp : 1≤(q+1)^2 := Nat.one_le_pow 2 (q+1) (by omega)
  have hm := Nat.mul_le_mul_right (B+5) (Nat.mul_le_mul_left 20 hp)
  have hw := wt_nat_le v
  unfold itCfObjB
  omega

/-- The actual bounded-object profile fits stage one before examining either
object's byte representation. -/
theorem itcs_obj_bound_stage (pf : Prim) (Bc Br : ℕ → ℕ)
    (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W q B : ℕ) (hq : q≤2*W+3) (hB : B≤2*(2*W+3)^64) :
    itCfObjB q B≤ itcsGrow pf Bc Br hBc hBr (W+100) := by
  have hb : itCfObjB q B≤ itCfObjB (2*W+3) (2*(2*W+3)^64) := by
    unfold itCfObjB
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 20
      (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
      (Nat.add_le_add_right hB 5)
  exact hb.trans (itcs_parent_profile pf Bc Br hBc hBr W (f:=fun W => itCfObjB (2*W+3) (2*(2*W+3)^64))
    (List.mem_of_getElem? (show (itcsCostFns pf Bc Br)[19]?=
      some (fun W => itCfObjB (2*W+3) (2*(2*W+3)^64)) from rfl)))

/-- The fixed answer profile increases with the physical degree. -/
theorem itcs_answer_cost_mono {k k' : ℕ} (hk : k≤ k') : ansW k≤ ansW k' := by
  simp only [ansW,groupW]
  gcongr

/-- All side-color tables have values at most two. -/
theorem itcs_side_color_le {q : ℕ} (W R : Finset (Fin q)) (a : Fin q) : itcsSide W R a≤2 := by
  classical
  unfold itcsSide
  split_ifs <;> omega

/-- The source and target side tables satisfy the concrete alignment program's
common input bound at the parent profile. -/
theorem itcs_side_align_weight {q W₀ : ℕ} (W R : Finset (Fin q)) (hq : q≤2*W₀+3) :
    (encFun (itcsSide W R)).wt≤100*(2*W₀+4)^2 := by
  have h : (encFun (itcsSide W R)).wt≤9*q+4 := by
    simpa only [Nat.mul_comm] using wt_encFun_le (itcsSide W R) (itcs_side_color_le W R)
  have hp : 2*W₀+4≤(2*W₀+4)^2 := Nat.le_self_pow (by decide : 2≠0) _
  omega

/-- The label-degree literal has a small parent polynomial weight. -/
theorem itcs_nat_parent_weight {q W : ℕ} (hq : q≤2*W+3) :
    (Val.nat q).wt≤100*(W+3)^2 := by
  have h := wt_nat_le q
  have hp : W+3≤(W+3)^2 := Nat.le_self_pow (by decide : 2≠0) _
  omega

/-- Both the alignment and twist permutation bytes fit a small parent profile. -/
theorem itcs_perm_parent_weight {q W : ℕ} (hq : q≤2*W+3) :
    4*(q+1)^2≤16*(W+2)^2 := by
  have h := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2)
  have he : 4*(2*W+3+1)^2=16*(W+2)^2 := by ring
  exact h.trans_eq he

end GI.Impl
