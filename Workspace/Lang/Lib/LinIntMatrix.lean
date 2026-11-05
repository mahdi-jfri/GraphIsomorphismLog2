module

public import Workspace.Lang.Lib.LinIntRowMul

@[expose] public section

/-! Dense integer matrix multiplication. The map context stores the column count
and the right matrix. Each left row runs the proved row-times-matrix program. -/
namespace GI.Lang
open GI.Cited (Val encInt encIntMatrix)
open Matrix

/-- On [[column-count,right-matrix],left-row], compute that row of the product. -/
def linMatrixRowF (row : ℕ) : Expr :=
  .call row (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1)))

def linMatrixMulFuns (b row : ℕ) : List Expr := mapFuns b (b + 3) ++ [linMatrixRowF row]

def linMatrixMulRowCost (W r c : ℕ) : ℕ := linRowMulCost (6 * W + 7) r c

def linMatrixMulCost (W m r c : ℕ) : ℕ :=
  let C := linMatrixMulRowCost W r c
  m * (1000 * (W + C + 1)) + mapK * (m + 1) * (W + linVectorAccWt m C + 1)

set_option maxHeartbeats 2000000 in
/-- Matrix product on [[[c,B],A]], with a polynomial bit cost in the dense dimensions.
This is a real map of row programs. No matrix-multiplication primitive is assumed. -/
theorem linMatrixMul_spec {P : Program} {b row column dot ib m r c : ℕ}
    (h : linIntSpec P ib) (hp : P.HasAt b (linMatrixMulFuns b row))
    (hrow : P.HasAt row (linRowMulFuns row column dot))
    (hcol : P.HasAt column (linColumnFuns column))
    (hdot : P.HasAt dot (linDotLoopFuns dot ib))
    (A : Matrix (Fin m) (Fin r) ℤ) (B : Matrix (Fin r) (Fin c) ℤ) :
    FunDet P b (.list [.list [.nat c, encIntMatrix B], encIntMatrix A]) (encIntMatrix (A * B))
      (linMatrixMulCost (Val.list [.list [.nat c, encIntMatrix B], encIntMatrix A]).wt m r c) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := hp.left
  have hf : P.funs[b + 3]? = some (linMatrixRowF row) := by simpa [mapFuns, loopFuns] using hp.right.single
  let ctx := Val.list [.nat c, encIntMatrix B]
  let W := (Val.list [ctx, encIntMatrix A]).wt
  let C := linMatrixMulRowCost W r c
  have wctx : ctx.wt < W := wt_le_wt_list (by simp)
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp)
  have wc : (Val.nat c).wt < W :=
    (wt_le_wt_list (vs := [.nat c, encIntMatrix B]) (v := .nat c) (by simp)).trans wctx
  have wB : (encIntMatrix B).wt < W :=
    (wt_le_wt_list (vs := [.nat c, encIntMatrix B]) (v := encIntMatrix B) (by simp)).trans wctx
  have wx (i : Fin m) : (linVecVal (A i)).wt < W := by
    have hh : (linVecVal (A i)).wt < (encIntMatrix A).wt :=
      wt_le_wt_list (by exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    exact hh.trans wA
  have rowCost (i : Fin m) :
      linRowMulCost (Val.list [.nat c, linVecVal (A i), encIntMatrix B]).wt r c ≤ C := by
    apply linRowMulCost_mono
    have hh := wt_list3_le (.nat c) (linVecVal (A i)) (encIntMatrix B)
    have hw := wx i
    omega
  have rowWt (i : Fin m) : (linVecVal ((A i) ᵥ* B)).wt ≤ C :=
    (linRowMul_spec h hrow hcol hdot (A i) B).wt_lt.le.trans (rowCost i)
  have hs : ∀ v ∈ (List.finRange m).map (fun i => linVecVal (A i)),
      FunAll P (b + 3) (.list [ctx, v]) (fun w cost =>
        (∀ i : Fin m, v = linVecVal (A i) → w = linVecVal ((A i) ᵥ* B)) ∧
          cost ≤ 1000 * (W + C + 1)) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have dc := Det.get' (Det.arg' (P := P) (vs := [ctx, linVecVal (A i)]) (rest := []) (j := 0) rfl)
      (Det.nat 0) (show [Val.nat c, encIntMatrix B][0]? = _ from rfl)
    have db := Det.get' (Det.arg' (P := P) (vs := [ctx, linVecVal (A i)]) (rest := []) (j := 0) rfl)
      (Det.nat 1) (show [Val.nat c, encIntMatrix B][1]? = _ from rfl)
    have dx := Det.arg' (P := P) (vs := [ctx, linVecVal (A i)]) (rest := []) (j := 1) rfl
    have d := Det.call (Det.mk3 dc dx db) (linRowMul_spec h hrow hcol hdot (A i) B)
    have winput := wt_list2_le ctx (linVecVal (A i))
    have warg := wt_list3_le (.nat c) (linVecVal (A i)) (encIntMatrix B)
    have wi := wx i
    have wo := rowWt i
    have hcost := rowCost i
    refine FunAll.mono (FunDet.intro hf d) fun w cost hw => ⟨?_, ?_⟩
    · intro k hk
      have he := linVecVal_injective hk
      rw [hw.1, he]
    · omega
  have hm := map_spec hmap hs
  refine hm.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have he : ws = (List.finRange m).map (fun i => linVecVal ((A i) ᵥ* B)) :=
    forall₂_map_eq (h := hws) (fun i _ w hw => hw i rfl)
  subst ws
  refine ⟨rfl, ?_⟩
  have wo := linWtList (vs := (List.finRange m).map (fun i => linVecVal ((A i) ᵥ* B))) (B := C) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact rowWt i)
  simp only [List.map_const', List.length_map, List.length_finRange, List.sum_replicate,
    smul_eq_mul] at hc wo
  unfold linMatrixMulCost linVectorAccWt
  change cost ≤ m * (1000 * (W + C + 1)) + mapK * (m + 1) *
    (W + (Val.list ((List.finRange m).map fun i => linVecVal ((A i) ᵥ* B))).wt + 1) at hc
  change cost ≤ m * (1000 * (W + C + 1)) + mapK * (m + 1) * (W + (2 * (m * C) + m + 4) + 1)
  have hh := Nat.mul_le_mul_left (mapK * (m + 1)) wo
  nlinarith

end GI.Lang
