import Workspace.Lang.Lib.LinIntDot

namespace GI.Lang
open GI.Cited (Val encInt encIntMatrix)

/-- The row encoding is injective, including for the empty row. -/
theorem linVecVal_injective {n : ℕ} : Function.Injective (linVecVal (n := n)) := by
  intro x y hxy
  simp only [linVecVal, Val.list.injEq, List.map_inj_left] at hxy
  funext i
  exact encInt_injective (hxy i (List.mem_finRange i))

/-- Read one coordinate of an integer row. The index is a natural input value. -/
def linColumnGetF : Expr := .get (arg 1) (arg 0)

theorem linColumnGet_spec {P : Program} {f n : ℕ}
    (hf : P.funs[f]? = some linColumnGetF) (x : Fin n → ℤ) (j : Fin n) :
    FunDet P f (.list [.nat j.val, linVecVal x]) (encInt (x j))
      (100 * ((Val.list [.nat j.val, linVecVal x]).wt + 1)) := by
  have dx := Det.arg' (P := P) (vs := [.nat j.val, linVecVal x]) (rest := []) (j := 1) rfl
  have dj := Det.arg' (P := P) (vs := [.nat j.val, linVecVal x]) (rest := []) (j := 0) rfl
  have he : ((List.finRange n).map fun i => encInt (x i))[j.val]? = some (encInt (x j)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using j.isLt)]
    simp
  have d := Det.get' dx dj he
  have wx := linVecEntryWt x j
  have wv := wt_le_wt_list (vs := [.nat j.val, linVecVal x]) (v := linVecVal x) (by simp)
  apply FunDet.intro hf
  exact d.mono (by omega)

/-- Map the coordinate getter over matrix rows to extract one column. -/
def linColumnFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [linColumnGetF]

def linColumnCost (W r : ℕ) : ℕ :=
  r * (100 * (4 * W + 7)) + mapK * (r + 1) * (W + linVectorAccWt r W + 1)

/-- Extract column j in polynomial bit cost. -/
theorem linColumn_spec {P : Program} {b r c : ℕ}
    (hp : P.HasAt b (linColumnFuns b)) (M : Matrix (Fin r) (Fin c) ℤ) (j : Fin c) :
    FunDet P b (.list [.nat j.val, encIntMatrix M]) (linVecVal fun i => M i j)
      (linColumnCost (Val.list [.nat j.val, encIntMatrix M]).wt r) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := hp.left
  have hget : P.funs[b + 3]? = some linColumnGetF := by simpa [mapFuns, loopFuns] using hp.right.single
  let W := (Val.list [.nat j.val, encIntMatrix M]).wt
  have wj : (Val.nat j.val).wt < W := wt_le_wt_list (by simp)
  have wM : (encIntMatrix M).wt < W := wt_le_wt_list (by simp)
  have wr (i : Fin r) : (linVecVal (M i)).wt < W := by
    have hi : (linVecVal (M i)).wt < (encIntMatrix M).wt := wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    exact hi.trans wM
  have hs : ∀ v ∈ (List.finRange r).map (fun i => linVecVal (M i)),
      FunAll P (b + 3) (.list [.nat j.val, v]) (fun w cost =>
        (∀ i : Fin r, v = linVecVal (M i) → w = encInt (M i j)) ∧ cost ≤ 100 * (4 * W + 7)) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have wa := wt_list2_le (.nat j.val) (linVecVal (M i))
    refine FunAll.mono (linColumnGet_spec hget (M i) j) fun w cost hw => ⟨?_, by have := wr i; omega⟩
    intro k hk
    have he := linVecVal_injective hk
    rw [hw.1, congrFun he j]
  have hm := map_spec hmap hs
  refine hm.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have he : ws = (List.finRange r).map (fun i => encInt (M i j)) :=
    forall₂_map_eq (h := hws) (fun i _ w hw => hw i rfl)
  subst ws
  refine ⟨rfl, ?_⟩
  have wo := linWtList (vs := (List.finRange r).map fun i => encInt (M i j)) (B := W) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact ((linVecEntryWt (M i) j).trans (wr i)).le)
  simp only [List.map_const', List.length_map, List.length_finRange, List.sum_replicate,
    smul_eq_mul] at hc wo
  unfold linColumnCost linVectorAccWt
  change cost ≤ r * (100 * (4 * W + 7)) + mapK * (r + 1) *
    (W + (Val.list ((List.finRange r).map fun i => encInt (M i j))).wt + 1) at hc
  change cost ≤ r * (100 * (4 * W + 7)) + mapK * (r + 1) * (W + (2 * (r * W) + r + 4) + 1)
  have hh := Nat.mul_le_mul_left (mapK * (r + 1)) wo
  nlinarith

theorem linColumnCost_mono {W V : ℕ} (h : W ≤ V) (r : ℕ) : linColumnCost W r ≤ linColumnCost V r := by
  unfold linColumnCost linVectorAccWt
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ (by omega)
  · exact Nat.mul_le_mul_left _ (by nlinarith)

end GI.Lang
