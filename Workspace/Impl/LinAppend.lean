module

public import Workspace.Impl.LinMapEncoded

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linAppendCost (W : ℕ) : ℕ := 100000 * (W + 1) ^ 2

theorem linAppend_spec {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b))
    (xs ys : List Val) : FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (linAppendCost (Val.list [.list xs, .list ys]).wt) := by
  let W := (Val.list [.list xs, .list ys]).wt
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp [W])
  have wy : (Val.list ys).wt < W := wt_le_wt_list (by simp [W])
  have hx := length_lt_wt_list xs
  have hy := length_lt_wt_list ys
  have hsx := sum_wt_lt_wt_list xs
  have hsy := sum_wt_lt_wt_list ys
  have wo := wt_list_le (xs ++ ys)
  simp only [List.map_append, List.sum_append, List.length_append] at wo
  refine (append_spec h xs ys).mono fun out cost ho => ⟨ho.1, ?_⟩
  have hc := ho.2
  rw [ho.1] at hc
  simp only [loopModK] at hc
  have hout : (Val.list (xs ++ ys)).wt ≤ 6 * W + 4 := by omega
  have hb := Nat.mul_le_mul (by omega : ys.length + 1 ≤ W + 1)
    (by omega : W + ys.length + (Val.list (xs ++ ys)).wt + 1 ≤ 8 * W + 5)
  change cost ≤ linAppendCost W
  unfold linAppendCost
  dsimp only [W] at *
  nlinarith

end GI.Impl
