import Workspace.Impl.LinPrimaryLoopArg
import Workspace.Impl.LinLoopInit

namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryLoopInitBudget (W : ℕ) : ℕ := 1000000 * (W + maxK * (W + 1) ^ 3 + 1)

set_option maxHeartbeats 1000000 in
theorem linPrimaryLoop_count_det {P : Program} {br d : ℕ} (h : P.HasAt br (maxFuns br))
    (v1 v2 v3 : Val) (p : ℕ) (ν : Fin d → ℕ)
    (hν : ∀ i, ν i ≤ (Val.list [v1, v2, v3, .nat p, encFun ν]).wt)
    (hd : d ≤ (Val.list [v1, v2, v3, .nat p, encFun ν]).wt) :
    let a := Val.list [v1, v2, v3, .nat p, encFun ν]
    Det P [a] (.call br (arg 4)) (.nat (linPrimaryHeight ν)) (linPrimaryLoopInitBudget a.wt) := by
  let a := Val.list [v1, v2, v3, .nat p, encFun ν]
  let W := a.wt
  have hm := max_spec h (xs := (List.finRange d).map ν) (B := W) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact hν i) (by simpa using hd)
  simp only [natList, List.map_map, Function.comp_def] at hm
  have dn := Det.arg' (P := P) (vs := [v1, v2, v3, .nat p, encFun ν]) (rest := []) (j := 4) rfl
  have dd := Det.call dn hm
  have hheight : linPrimaryHeight ν ≤ W := foldl_max_le (Nat.zero_le _) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact hν i)
  have wh := (wt_nat_le (linPrimaryHeight ν)).trans (Nat.add_le_add_right hheight 2)
  refine dd.mono ?_
  unfold linPrimaryLoopInitBudget
  dsimp only [a, W, linPrimaryHeight] at *
  omega

set_option maxHeartbeats 1000000 in
theorem linPrimaryLoop_start_det {P : Program} {d : ℕ} (v1 v2 v3 : Val) (p : ℕ) (ν : Fin d → ℕ) :
    let a := Val.list [v1, v2, v3, .nat p, encFun ν]
    Det P [a] (mk3 (arg 0) (arg 1) (arg 2)) (.list [v1, v2, v3]) (linPrimaryLoopInitBudget a.wt) := by
  let a := Val.list [v1, v2, v3, .nat p, encFun ν]
  have d1 := Det.arg' (P := P) (vs := [v1, v2, v3, .nat p, encFun ν]) (rest := []) (j := 0) rfl
  have d2 := Det.arg' (P := P) (vs := [v1, v2, v3, .nat p, encFun ν]) (rest := []) (j := 1) rfl
  have d3 := Det.arg' (P := P) (vs := [v1, v2, v3, .nat p, encFun ν]) (rest := []) (j := 2) rfl
  have dd := Det.mk3 d1 d2 d3
  have hw : (Val.list [v1, v2, v3]).wt ≤ a.wt := wt_list_mono ⟨[.nat p, encFun ν], rfl⟩
  refine dd.mono ?_
  unfold linPrimaryLoopInitBudget
  dsimp only [a] at *
  omega

theorem linPrimaryLoopInitBudget_poly : PBU (fun _ W _ => linPrimaryLoopInitBudget W) := by
  unfold linPrimaryLoopInitBudget
  norm_poly

end GI.Impl
