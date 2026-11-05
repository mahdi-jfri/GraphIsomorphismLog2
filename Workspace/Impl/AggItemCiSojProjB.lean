module

public import Workspace.Impl.AggItemCiSojGM
public import Workspace.Impl.AggItemCiSojGW
public import Workspace.Impl.AggItemCiSojPR
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! # Uniform polynomial bounds for processing one canonical rectangle answer -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The normalized-factor lift bound is monotone in its size argument. -/
theorem itcs_lift_cost_mono (pf : Prim) {a b : ℕ} (h : a≤ b) : liftLabCost pf a≤ liftLabCost pf b := by
  unfold liftLabCost
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left h 4)) 2) _)
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)

/-- One exact physical-to-label projection. -/
def itcsLiftB (pf : Prim) (U : ℕ) : ℕ := liftLabCost pf (3*U+2)

/-- Mapping a canonical generator list. -/
def itcsGenMapB (pf : Prim) (U : ℕ) : ℕ :=
  (U+1)*itcsLiftB pf U+mapK*(U+2)*(10*U+10)

/-- Rebuilding the projected group encoding. -/
def itcsGroupMapB (pf : Prim) (U : ℕ) : ℕ :=
  50*(100*(4*U+10)+1)+itcsGenMapB pf U

/-- Processing a complete canonical answer, including the empty case. -/
def itcsProjectB (pf : Prim) (U : ℕ) : ℕ :=
  100*(1000*(3*U+(2*U+1)^2+10)+1)+itcsLiftB pf U+itcsGroupMapB pf U+
    permK*(U+1)^3+20*(4*U+8*(U+1)^2+17)

/-- A polynomial local input envelope for the projected generator encoding. -/
def itcsProjU (W : ℕ) : ℕ := 1000*(W+20)^4

/-- The answer processor's uniform local-input bound. -/
def itcsProcessC (pf : Prim) (W : ℕ) : ℕ := itcsProjectB pf (itcsProjU W)

/-- Every term in the generator map is bounded by the same scalar envelope. -/
theorem itcs_gen_map_bound (pf : Prim) {k q l n U : ℕ} (ctx gv out : Val)
    (hk:k≤ U) (hq:q≤ U) (hl:l≤ U) (hn:n≤ U)
    (hc:ctx.wt≤ U) (hg:gv.wt≤ U) (ho:out.wt≤ U) :
    itcsGenMapC pf k q l n ctx gv out≤ itcsGenMapB pf U := by
  have hw:=wt_list2_le ctx gv
  have hp:=itcs_lift_cost_mono pf (by omega : l+q+k+2≤3*U+2)
  unfold itcsGenMapC itcsGenMapB itcsLiftB
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) hp)
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))

/-- The group wrapper only increases the common envelope polynomially. -/
theorem itcs_group_map_bound (pf : Prim) {q U Cg : ℕ} (ctx gv out : Val)
    (hq:q≤ U) (hc:ctx.wt≤ U) (hg:gv.wt≤ U) (ho:out.wt≤ U)
    (hC:Cg≤ itcsGenMapB pf U) :
    50*(itcsGroupMapW q ctx gv out+1)+Cg≤ itcsGroupMapB pf U := by
  unfold itcsGroupMapW itcsGroupMapB
  omega

/-- The representative/group projector is bounded uniformly in all its encoded data. -/
theorem itcs_project_bound (pf : Prim) {k q U Cp Cg : ℕ} (ctx gv out : Val)
    (hk:k≤ U) (hq:q≤ U) (hc:ctx.wt≤ U) (hg:gv.wt≤ U) (ho:out.wt≤ U)
    (hp:Cp≤ itcsLiftB pf U) (hgm:Cg≤ itcsGroupMapB pf U) :
    100*(itcsProjectW k q ctx gv out+1)+Cp+Cg+permK*(q+1)^3≤ itcsProjectB pf U := by
  have hs:=Nat.pow_le_pow_left (by omega : k+q+1≤2*U+1) 2
  have hq3:=Nat.mul_le_mul_left permK (Nat.pow_le_pow_left (by omega : q+1≤ U+1) 3)
  unfold itcsProjectW itcsProjectB
  omega

/-- The local input envelope dominates the input itself. -/
theorem itcs_proj_u_ge (W : ℕ) : W+20≤ itcsProjU W := by
  have h:=Nat.le_self_pow (by decide : 4≠0) (W+20)
  unfold itcsProjU
  omega

/-- The complete answer-processing bound is a polynomial of local input weight.
The primitive's fixed coefficient and exponent remain fixed constants. -/
theorem itcs_process_pbu (pf : Prim) : PBU fun _ W _=>itcsProcessC pf W := by
  simp only [itcsProcessC,itcsProjectB,itcsProjU,itcsLiftB,itcsGroupMapB,itcsGenMapB,
    liftLabCost,liftLabK,mapK,permK]
  norm_poly

/-- Increasing the local input budget preserves the processing bound. -/
theorem itcs_process_mono (pf : Prim) {a b : ℕ} (h : a ≤ b) :
    itcsProcessC pf a ≤ itcsProcessC pf b := by
  unfold itcsProcessC itcsProjectB itcsProjU itcsLiftB itcsGroupMapB itcsGenMapB
    liftLabCost
  gcongr
  unfold itcsLiftB
  apply itcs_lift_cost_mono
  gcongr

end GI.Impl
