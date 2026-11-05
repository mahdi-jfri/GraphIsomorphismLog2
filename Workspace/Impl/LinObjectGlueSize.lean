module

public import Workspace.Impl.LinObjectGluePrefix

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

variable {n : ℕ} (I : linObjectGlueProblem n)

theorem linObjectGlueProblem.size_bounds : n ≤ I.value.wt ∧ I.Y.length+I.X.length ≤ I.value.wt := by
  have wa : (encGroup I.as).wt < I.value.wt := wt_le_wt_list (by simp [linObjectGlueProblem.value,tmGlIn])
  have wn := S_le_wt_encGroup I.as
  have hn : n+1 ≤ (I.as.length+2)*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
  have hx := length_lt_wt_list (I.X.map tmGlObjVal)
  have hy := length_lt_wt_list (I.Y.map tmGlObjVal)
  simp only [List.length_map] at hx hy
  have hsum := sum_wt_lt_wt_list [encGroup I.hs,encGroup I.ns,encGroup I.as,tmGlObjsVal I.X,
    tmGlObjsVal I.Y,encGroup I.bs,encPerm I.τ]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hsum
  change _ < I.value.wt at hsum
  change I.X.length < (tmGlObjsVal I.X).wt at hx
  change I.Y.length < (tmGlObjsVal I.Y).wt at hy
  constructor <;> omega

open scoped IsMulCommutative
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

theorem linObjectGlueFrame.dimension_le (F : linObjectGlueFrame I.as I.ns I.Y) :
    I.as.length*(tmRiPcsO (gens I.as) I.Y).length ≤ F.value.wt := by
  have hw : (linVecVal (fun i => F.D i i)).wt ≤ F.value.wt := normReadVal_wt (path:=[4,0]) rfl
  have hh := length_lt_wt_list ((List.finRange (I.as.length*(tmRiPcsO (gens I.as) I.Y).length)).map fun i => encInt (F.D i i))
  simp only [List.length_map,List.length_finRange] at hh
  change _ < (linVecVal (fun i => F.D i i)).wt at hh
  omega

theorem linFiniteIntVecVal_zero {d : ℕ} (m : Fin d → ℕ) :
    linFiniteIntVecVal m 0 = linVecVal (0 : Fin d → ℤ) := by
  unfold linFiniteIntVecVal
  congr 1
  funext i
  simp

end GI.Impl
