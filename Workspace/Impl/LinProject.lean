module

public import Workspace.Impl.LinMapSource
public import Workspace.Lang.Lib.LinIntColumn

@[expose] public section

/-! Select one field from each stored record, without assuming that records
encode their source group elements injectively. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linProjectFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [linColumnGetF]

theorem linProjectFuns_length (b : ℕ) : (linProjectFuns b).length = 4 := rfl

def linProjectCost (W : ℕ) : ℕ := linMapBudget W (10000 * (W + 1))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linProject_spec {P : Program} {b : ℕ} {α : Type}
    (h : P.HasAt b (linProjectFuns b)) (j : ℕ) (rows : α → List Val) (out : α → Val)
    (xs : List α) (hget : ∀ x ∈ xs, (rows x)[j]? = some (out x)) :
    FunDet P b (.list [.nat j, .list (xs.map fun x => .list (rows x))])
      (.list (xs.map out))
      (linProjectCost (Val.list [.nat j, .list (xs.map fun x => .list (rows x))]).wt) := by
  let a := Val.list [.nat j, .list (xs.map fun x => .list (rows x))]
  let W := a.wt
  have hm : P.HasAt b (mapFuns b (b + 3)) := h.block 0 rfl
  have hg : P.funs[b + 3]? = some linColumnGetF := (h.block (gs := [linColumnGetF]) 3 rfl).single
  apply linMapSource_spec hm (fun x => .list (rows x)) out (.nat j) xs (10000 * (W + 1))
  intro x hx
  have wrs : (Val.list (xs.map fun x => .list (rows x))).wt < W := wt_le_wt_list (by simp [W, a])
  have wr : (Val.list (rows x)).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)).trans wrs
  have wj : (Val.nat j).wt < W := wt_le_wt_list (by simp [W, a])
  have wo : (out x).wt < (Val.list (rows x)).wt :=
    wt_le_wt_list (List.mem_of_getElem? (hget x hx))
  have dw := Det.arg' (P := P) (vs := [.nat j, .list (rows x)]) (rest := []) (j := 1) rfl
  have dj := Det.arg' (P := P) (vs := [.nat j, .list (rows x)]) (rest := []) (j := 0) rfl
  have dd := Det.get' dw dj (hget x hx)
  have wa := wt_list2_le (.nat j) (.list (rows x))
  apply FunDet.intro hg
  refine dd.mono ?_
  dsimp only [W, a] at *
  omega

theorem linProjectCost_mono {W V : ℕ} (h : W ≤ V) : linProjectCost W ≤ linProjectCost V := by
  unfold linProjectCost linMapBudget
  gcongr

theorem linProjectCost_poly : PBU (fun _ W _ => linProjectCost W) := by
  unfold linProjectCost linMapBudget
  norm_poly

end GI.Impl
