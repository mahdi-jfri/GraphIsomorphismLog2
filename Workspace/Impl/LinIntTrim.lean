module

public import Workspace.Impl.LinIntTriMath

@[expose] public section

set_option maxHeartbeats 2000000

namespace GI.Impl
open GI.Cited GI.Lang

/-- Tail of an integer row agrees with the successor-indexed vector. -/
theorem linTail_vec_spec {P : Program} {b n : ℕ} (hp : P.HasAt b (linTailFuns b))
    (x : Fin (n + 1) → ℤ) :
    FunDet P b (linVecVal x) (linVecVal fun i => x i.succ) (linTailCost (linVecVal x).wt) := by
  have ht := linTail_spec hp ((List.finRange (n + 1)).map fun i => encInt (x i))
  simpa only [linVecVal, List.finRange_succ, List.map_cons, List.drop_succ_cons, List.drop_zero,
    List.map_map, Function.comp_def] using ht

theorem linTailCost_mono {W V : ℕ} (h : W ≤ V) : linTailCost W ≤ linTailCost V := by
  unfold linTailCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

def linTrimRowF (tail : ℕ) : Expr := .call tail (arg 1)
def linTrimMapFuns (b tail : ℕ) : List Expr := mapFuns b (b + 3) ++ [linTrimRowF tail]

def linTrimMapCost (W r : ℕ) : ℕ :=
  r * (100 * (linTailCost W + W + 1)) + mapK * (r + 1) * (W + linVectorAccWt r W + 1)

/-- Remove the first column of each row. -/
theorem linTrimMap_spec {P : Program} {b tail r n : ℕ}
    (hp : P.HasAt b (linTrimMapFuns b tail)) (ht : P.HasAt tail (linTailFuns tail))
    (A : Matrix (Fin r) (Fin (n + 1)) ℤ) :
    FunDet P b (.list [.list [], encIntMatrix A]) (encIntMatrix fun i j => A i j.succ)
      (linTrimMapCost (Val.list [.list [], encIntMatrix A]).wt r) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := hp.left
  have hf : P.funs[b + 3]? = some (linTrimRowF tail) := by simpa [mapFuns, loopFuns] using hp.right.single
  let W := (Val.list [.list [], encIntMatrix A]).wt
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp)
  have wr (i : Fin r) : (linVecVal (A i)).wt < W := by
    have hh : (linVecVal (A i)).wt < (encIntMatrix A).wt :=
      wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    exact hh.trans wA
  have wt (i : Fin r) : (linVecVal fun j => A i j.succ).wt ≤ W := by
    have hsub : (linVecVal fun j => A i j.succ).wt ≤ (linVecVal (A i)).wt := by
      have hh := wt_list_sublist
        (List.drop_sublist 1 ((List.finRange (n + 1)).map fun j => encInt (A i j)))
      simpa only [linVecVal, List.finRange_succ, List.map_cons, List.drop_succ_cons, List.drop_zero,
        List.map_map, Function.comp_def] using hh
    exact hsub.trans (wr i).le
  have hs : ∀ v ∈ (List.finRange r).map (fun i => linVecVal (A i)),
      FunAll P (b + 3) (.list [.list [], v]) (fun w cost =>
        (∀ i : Fin r, v = linVecVal (A i) → w = linVecVal fun j => A i j.succ) ∧
          cost ≤ 100 * (linTailCost W + W + 1)) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have d := Det.call (Det.arg' (P := P) (vs := [.list [], linVecVal (A i)]) (rest := []) (j := 1) rfl)
      (linTail_vec_spec ht (A i))
    have wa := wt_list2_le (.list []) (linVecVal (A i))
    have wn : (Val.list []).wt = 4 := rfl
    have wi := wr i
    have wo := wt i
    have hc := linTailCost_mono wi.le
    refine FunAll.mono (FunDet.intro hf d) fun w cost hw => ⟨?_, by omega⟩
    intro k hk
    have he := linVecVal_injective hk
    rw [hw.1, he]
  have hm := map_spec hmap hs
  refine hm.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have he : ws = (List.finRange r).map (fun i => linVecVal fun j => A i j.succ) :=
    forall₂_map_eq (h := hws) (fun i _ w hw => hw i rfl)
  subst ws
  refine ⟨rfl, ?_⟩
  have wo := linWtList (vs := (List.finRange r).map (fun i => linVecVal fun j => A i j.succ)) (B := W) (by
    intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv; exact wt i)
  simp only [List.map_const', List.length_map, List.length_finRange, List.sum_replicate, smul_eq_mul] at hc wo
  unfold linTrimMapCost linVectorAccWt
  change cost ≤ r * (100 * (linTailCost W + W + 1)) + mapK * (r + 1) *
    (W + (Val.list ((List.finRange r).map fun i => linVecVal fun j => A i j.succ)).wt + 1) at hc
  change cost ≤ r * (100 * (linTailCost W + W + 1)) + mapK * (r + 1) * (W + (2 * (r * W) + r + 4) + 1)
  have hh := Nat.mul_le_mul_left (mapK * (r + 1)) wo
  nlinarith

theorem linTrimMapCost_mono {W V : ℕ} (h : W ≤ V) (r : ℕ) : linTrimMapCost W r ≤ linTrimMapCost V r := by
  have ht := linTailCost_mono h
  unfold linTrimMapCost linVectorAccWt
  exact Nat.add_le_add (Nat.mul_le_mul_left r (by omega)) (Nat.mul_le_mul_left _ (by nlinarith))

/-- Drop the first matrix row, then remove the first column from each remaining row. -/
def linTrimF (tail map : ℕ) : Expr :=
  .letE (.call tail (.var 0)) (.call map (mk2 .nil (.var 1)))

def linTrimCost (W n : ℕ) : ℕ := 100 * (linTailCost W + linTrimMapCost (2 * W + 14) n + W + 1)

/-- The matrix-trimming program returns exactly the pure solver's trailing block. -/
theorem linTrim_spec {P : Program} {f tail map n : ℕ}
    (hf : P.funs[f]? = some (linTrimF tail map)) (ht : P.HasAt tail (linTailFuns tail))
    (hm : P.HasAt map (linTrimMapFuns map tail))
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    FunDet P f (encIntMatrix H) (encIntMatrix (linTail H)) (linTrimCost (encIntMatrix H).wt n) := by
  let R : Matrix (Fin n) (Fin (n + 1)) ℤ := fun i j => H i.succ j
  have hd := linTail_spec ht ((List.finRange (n + 1)).map fun i => linVecVal (H i))
  simp only [List.finRange_succ, List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_map] at hd
  have htR : (encIntMatrix R).wt ≤ (encIntMatrix H).wt := by
    have hs := wt_list_sublist (List.drop_sublist 1 ((List.finRange (n + 1)).map fun i => linVecVal (H i)))
    simpa only [R, encIntMatrix, linVecVal, List.finRange_succ, List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_map, Function.comp_def] using hs
  have hd' : FunDet P tail (encIntMatrix H) (encIntMatrix R) (linTailCost (encIntMatrix H).wt) := by
    simpa only [R, encIntMatrix, linVecVal, List.finRange_succ, List.map_cons, List.drop_succ_cons,
      List.drop_zero, List.map_map, Function.comp_def] using hd
  have dm := linTrimMap_spec hm ht R
  have dc := Det.call (Det.var' (P := P) (env := [encIntMatrix H]) (i := 0) rfl) hd'
  have ds := Det.call (Det.mk2 Det.nil
    (Det.var' (P := P) (env := [encIntMatrix H, encIntMatrix R]) (i := 1) rfl)) dm
  apply FunDet.intro hf
  refine (Det.letE dc ds).mono ?_
  have wi := wt_list2_le (.list []) (encIntMatrix R)
  have wn : (Val.list []).wt = 4 := rfl
  have hc := linTrimMapCost_mono (show (Val.list [.list [], encIntMatrix R]).wt ≤
      2 * (encIntMatrix H).wt + 14 by omega) n
  have wo := dm.wt_lt
  unfold linTrimCost
  omega

attribute [gcongr] linTailCost_mono

theorem linTrimMapCost_mono_both {W V r s : ℕ} (hW : W ≤ V) (hr : r ≤ s) :
    linTrimMapCost W r ≤ linTrimMapCost V s := by
  unfold linTrimMapCost linVectorAccWt
  gcongr

attribute [gcongr] linTrimMapCost_mono_both

theorem linTrimCost_mono {W V n m : ℕ} (hW : W ≤ V) (hn : n ≤ m) : linTrimCost W n ≤ linTrimCost V m := by
  unfold linTrimCost
  gcongr

end GI.Impl
