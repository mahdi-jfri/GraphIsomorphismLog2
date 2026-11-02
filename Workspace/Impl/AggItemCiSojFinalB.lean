import Workspace.Impl.AggItemCiSojAnswersB
import Workspace.Impl.AggItemCiSojFinishN
import Workspace.Impl.AggItemCiSojGFRows
import Workspace.Impl.AggItemCiSojRF

/-! # Uniform local-input costs for the full rectangle-answer finalizer -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- Filter cost when list length and argument weight are bounded by `n`. -/
def itcsFilterB (n : ℕ) : ℕ := n*(100*(n+10))+loopModK*(n+1)*(3*n+1)

/-- First-field map cost, including a conservative bound for its result list. -/
def itcsFirstB (n : ℕ) : ℕ :=
  n*(100*(4*n+20))+mapK*(n+1)*(n+(n*(2*n+1)+4)+1)

/-- Overcoset map cost, including all output permutation tables. -/
def itcsOverB (n : ℕ) : ℕ :=
  n*(50*(100*(n+12*(n+1)^2+10)+1)+permK*(n+1)^3)+mapK*(n+1)*
    (n+(n*(2*(2*(4*(n+1)^2+n)+6)+1)+4)+1)

/-- Cost of the fixed finalizer wrapper after all five callee bounds fit `n`. -/
def itcsFinishB (n : ℕ) : ℕ := 200*(100*(6*n+100)+1)+5*n

/-- Scalar substitution for the actual empty-row filter cost. -/
theorem itcs_filter_bound {n C W : ℕ} (hn : n≤ W) (hc : C≤ W) :
    n*(100*(C+10))+loopModK*(n+1)*(2*C+n+1) ≤ itcsFilterB W := by
  unfold itcsFilterB
  gcongr
  omega

/-- Scalar substitution for the first-field map cost. -/
theorem itcs_first_bound {n C out W : ℕ} (hn : n≤ W) (hc : C≤ W)
    (ho : out≤ W*(2*W+1)+4) :
    n*(100*(4*C+20))+mapK*(n+1)*(C+out+1) ≤ itcsFirstB W := by
  unfold itcsFirstB
  gcongr

/-- The group constructor is monotone in its actual scalar size. -/
theorem itcs_group_build_mono {a b : ℕ} (h : a≤ b) : itcsGroupBuildC a≤ itcsGroupBuildC b := by
  unfold itcsGroupBuildC
  gcongr

/-- Scalar substitution for the complete nonempty finalizer wrapper cost. -/
theorem itcs_finish_bound {W Cr Cf Cp Cg Co n : ℕ}
    (hW : W≤ n) (hr : Cr≤ n) (hf : Cf≤ n) (hp : Cp≤ n) (hg : Cg≤ n) (ho : Co≤ n) :
    200*(100*(W+Cr+Cf+Cp+Cg+Co+100)+1)+Cr+Cf+Cp+Cg+Co ≤ itcsFinishB n := by
  unfold itcsFinishB
  omega

/-- The empty finalizer branch fits the same fixed wrapper budget. -/
theorem itcs_finish_empty_bound {W Cr Cf n : ℕ} (hW : W≤ n) (hr : Cr≤ n) (hf : Cf≤ n) :
    50*(100*(W+Cr+Cf+100)+1)+Cr+Cf ≤ itcsFinishB n := by
  unfold itcsFinishB
  omega

/-- All scalar list-wrapper bounds are fixed polynomials. -/
theorem itcs_filter_pbu : PBU fun k _ _ => itcsFilterB k := by
  unfold itcsFilterB
  norm_poly

theorem itcs_first_pbu : PBU fun k _ _ => itcsFirstB k := by
  unfold itcsFirstB
  norm_poly

theorem itcs_over_pbu : PBU fun k _ _ => itcsOverB k := by
  unfold itcsOverB
  norm_poly

theorem itcs_finish_pbu : PBU fun k _ _ => itcsFinishB k := by
  unfold itcsFinishB
  norm_poly

theorem itcs_group_local_pbu : PBU fun k _ _ => itcsGroupBuildC (10*k+10) := by
  unfold itcsGroupBuildC
  norm_poly

/-- Successive argument-weight envelopes for the five full finalizer calls. -/
def itcsFinalU0 (pf : Prim) (W : ℕ) : ℕ := 10*(W+itcsRowsBound pf W+100)
def itcsFinalU1 (pf : Prim) (W : ℕ) : ℕ := 10*(itcsFinalU0 pf W+itcsFilterB (itcsFinalU0 pf W)+100)
def itcsFinalU2 (pf : Prim) (W : ℕ) : ℕ := 10*(itcsFinalU1 pf W+itcsFirstB (itcsFinalU1 pf W)+100)
def itcsFinalU3 (pf : Prim) (W : ℕ) : ℕ := 10*(itcsFinalU2 pf W+itcsGroupBuildC (10*itcsFinalU2 pf W+10)+100)
def itcsFinalU4 (pf : Prim) (W : ℕ) : ℕ := 10*(itcsFinalU3 pf W+itcsOverB (itcsFinalU3 pf W)+100)

/-- The complete local-input budget for the actual finalizer. -/
def itcsFinalC (pf : Prim) (W : ℕ) : ℕ := itcsFinishB (itcsFinalU4 pf W)

set_option maxRecDepth 4096 in
/-- The full finalizer budget is polynomial in its actual encoded input weight. -/
theorem itcs_final_pbu (pf : Prim) : PBU fun _ W _ => itcsFinalC pf W := by
  have h0 : PBU fun _ W _ => itcsFinalU0 pf W := PBU.smul 10 (PBU.addc (PBU.add PBU.W (itcs_answers_pbu pf)) 100)
  have h1 : PBU fun _ W _ => itcsFinalU1 pf W := PBU.smul 10 (PBU.addc (PBU.add h0 (normPoly_comp (f:=itcsFilterB) (g:=fun _ W _ => itcsFinalU0 pf W) itcs_filter_pbu h0)) 100)
  have h2 : PBU fun _ W _ => itcsFinalU2 pf W := PBU.smul 10 (PBU.addc (PBU.add h1 (normPoly_comp (f:=itcsFirstB) (g:=fun _ W _ => itcsFinalU1 pf W) itcs_first_pbu h1)) 100)
  have h3 : PBU fun _ W _ => itcsFinalU3 pf W := PBU.smul 10 (PBU.addc (PBU.add h2 (normPoly_comp (f:=(fun W => itcsGroupBuildC (10*W+10))) (g:=fun _ W _ => itcsFinalU2 pf W) itcs_group_local_pbu h2)) 100)
  have h4 : PBU fun _ W _ => itcsFinalU4 pf W := PBU.smul 10 (PBU.addc (PBU.add h3 (normPoly_comp (f:=itcsOverB) (g:=fun _ W _ => itcsFinalU3 pf W) itcs_over_pbu h3)) 100)
  exact normPoly_comp (f:=itcsFinishB) (g:=fun _ W _ => itcsFinalU4 pf W) itcs_finish_pbu h4

end GI.Impl
