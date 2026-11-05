module

public import Workspace.Impl.LinTabulate
public import Workspace.Lang.Lib.LinIntVector
public import Workspace.Lang.Lib.LinIntTests
public import Workspace.Impl.LinPresentation

@[expose] public section

/-! Zero padding of local coordinate matrices. Different local stabilizers
may have different generator counts; padding puts all blocks in one shape. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linObjectPadMatrix {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) (R : ℕ) :
    Matrix (Fin R) (Fin d) ℤ := fun i j => if h : i.val < r then M ⟨i.val, h⟩ j else 0

def linObjectPadCellF : Expr :=
  .ite (.arith .lt (arg 1) (.length (.get (arg 0) (.nat 0))))
    (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))

def linObjectPadF (rep tab : ℕ) : Expr :=
  .letE (.call rep (mk2 (.length (arg 1)) linIntZeroE))
    (.call tab (mk2 (mk2 (arg 2) (.var 1)) (.length (arg 0))))

def linObjectPadFuns (b : ℕ) : List Expr :=
  [linObjectPadF (b + 2) (b + 5), linObjectPadCellF] ++
    replicateFuns (b + 2) ++ linTabulateFuns (b + 5) (b + 1)

theorem linObjectPadFuns_length (b : ℕ) : (linObjectPadFuns b).length = 12 := rfl

structure linObjectPadAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectPadF (b + 2) (b + 5))
  cell : P.funs[b + 1]? = some linObjectPadCellF
  rep : P.HasAt (b + 2) (replicateFuns (b + 2))
  tab : linTabulateAt P (b + 5) (b + 1)

theorem linObjectPadAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linObjectPadFuns b)) : linObjectPadAt P b where
  entry := (h.block (gs := [linObjectPadF (b + 2) (b + 5)]) 0 rfl).single
  cell := (h.block (gs := [linObjectPadCellF]) 1 rfl).single
  rep := h.block 2 rfl
  tab := linTabulateAt_of (h.block 5 rfl)

set_option maxHeartbeats 1000000 in
theorem linObjectPadCell_spec {P : Program} {f r d R : ℕ}
    (hf : P.funs[f]? = some linObjectPadCellF) (M : Matrix (Fin r) (Fin d) ℤ)
    (i : Fin R) :
    let a := Val.list [.list [encIntMatrix M, linVecVal (0 : Fin d → ℤ)], .nat i]
    FunDet P f a (linVecVal (linObjectPadMatrix M R i)) (100000 * (a.wt + 1)) := by
  let ctx := Val.list [encIntMatrix M, linVecVal (0 : Fin d → ℤ)]
  let a := Val.list [ctx, .nat i]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp [a, W])
  have wm : (encIntMatrix M).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wz : (linVecVal (0 : Fin d → ℤ)).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have hr : r < (encIntMatrix M).wt := by
    have hh := length_lt_wt_list ((List.finRange r).map fun i => linVecVal (M i))
    simpa only [encIntMatrix, linVecVal, List.length_map, List.length_finRange] using hh
  have dc := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have dm := Det.get' dc (Det.nat 0) rfl
  have dl := Det.length dm
  simp only [List.length_map, List.length_finRange] at dl
  have dz := Det.get' dc (Det.nat 1) rfl
  have dlt := Det.arith (op := .lt) di dl
  have hw0 : (Val.nat 0).wt = 2 := rfl
  have hw1 : (Val.nat 1).wt = 3 := rfl
  apply FunDet.intro hf
  by_cases hi : i.val < r
  · have hb : GI.Machine.BinOp.lt.eval i.val r = 1 := by simp [GI.Machine.BinOp.eval, hi]
    rw [hb] at dlt
    have de := Det.get' dm di (v := linVecVal (M ⟨i.val, hi⟩)) (by
      simp [encIntMatrix, linVecVal, hi])
    have dr := Det.ite_pos dlt (by decide : 1 ≠ 0) de
      (e := .get (arg 0) (.nat 1))
    have wo : (linVecVal (M ⟨i.val, hi⟩)).wt < (encIntMatrix M).wt := wt_le_wt_list (by
      change linVecVal (M ⟨i.val, hi⟩) ∈ (List.finRange r).map (fun j => linVecVal (M j))
      exact List.mem_map.mpr ⟨⟨i.val, hi⟩, List.mem_finRange _, rfl⟩)
    have hrn := wt_nat_le r
    have he : linVecVal (linObjectPadMatrix M R i) = linVecVal (M ⟨i.val, hi⟩) := by
      congr 1; ext j; simp [linObjectPadMatrix, hi]
    rw [he]
    exact dr.mono (by dsimp only [a, W, ctx] at *; omega)
  · have hb : GI.Machine.BinOp.lt.eval i.val r = 0 := by simp [GI.Machine.BinOp.eval, hi]
    rw [hb] at dlt
    have dr := Det.ite_zero dlt dz (t := .get (.get (arg 0) (.nat 0)) (arg 1))
    have hrn := wt_nat_le r
    have he : linVecVal (linObjectPadMatrix M R i) = linVecVal (0 : Fin d → ℤ) := by
      congr 1; ext j; simp [linObjectPadMatrix, hi]
    rw [he]
    exact dr.mono (by dsimp only [a, W, ctx] at *; omega)

theorem linObjectZeroRow_spec {P : Program} {b : ℕ}
    (h : P.HasAt b (replicateFuns b)) (d : ℕ) :
    FunDet P b (.list [.nat d, encInt 0]) (linVecVal (0 : Fin d → ℤ))
      (100000 * (d + 1) ^ 2) := by
  have hh := replicate_spec h d (encInt 0)
  have hz : (encInt 0).wt = 15 := by decide
  have hw := linWtList (vs := List.replicate d (encInt 0)) (B := 15) (by simp [hz])
  have wa := wt_list2_le (.nat d) (encInt 0)
  have hn := wt_nat_le d
  refine hh.mono fun out cost ho => ⟨?_, ?_⟩
  · simpa only [linVecVal, Pi.zero_apply, List.map_const', List.length_finRange] using ho.1
  · have hc := ho.2
    rw [ho.1] at hc
    simp only [List.length_replicate] at hw
    simp only [loopModK] at hc
    nlinarith

def linObjectPadZeroBudget (W : ℕ) : ℕ := 100000 * (W + 1) ^ 2
def linObjectPadArg (W : ℕ) : ℕ := 1000 * (W + linObjectPadZeroBudget W + 1)
def linObjectPadTabBudget (W : ℕ) : ℕ :=
  linTabulateCost (linObjectPadArg W) W (100000 * (linObjectPadArg W + 1))
def linObjectPadCost (W : ℕ) : ℕ :=
  100000 * (W + linObjectPadZeroBudget W + linObjectPadTabBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linObjectPad_spec {P : Program} {b r d R : ℕ}
    (h : linObjectPadAt P b) (M : Matrix (Fin r) (Fin d) ℤ) :
    let a := Val.list [encFun (fun i : Fin R => i.val),
      encFun (fun i : Fin d => i.val), encIntMatrix M]
    FunDet P b a (encIntMatrix (linObjectPadMatrix M R)) (linObjectPadCost a.wt) := by
  let ids := encFun (fun i : Fin R => i.val)
  let cols := encFun (fun i : Fin d => i.val)
  let a := Val.list [ids, cols, encIntMatrix M]
  let W := a.wt
  let zero := linVecVal (0 : Fin d → ℤ)
  let ctx := Val.list [encIntMatrix M, zero]
  have wi : ids.wt < W := wt_le_wt_list (by simp [a, W])
  have wc : cols.wt < W := wt_le_wt_list (by simp [a, W])
  have wm : (encIntMatrix M).wt < W := wt_le_wt_list (by simp [a, W])
  have hR : R ≤ W := by
    have hh := length_lt_wt_list ((List.finRange R).map fun i => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change R < ids.wt at hh
    omega
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change d < cols.wt at hh
    omega
  have hz := (linObjectZeroRow_spec h.rep d).mono
    (show 100000 * (d + 1) ^ 2 ≤ linObjectPadZeroBudget W from
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wz : zero.wt ≤ linObjectPadZeroBudget W := hz.wt_lt.le
  have harg : (Val.list [ctx, .nat R]).wt ≤ linObjectPadArg W := by
    have hctx := wt_list2_le (encIntMatrix M) zero
    have ha := wt_list2_le ctx (.nat R)
    have hn := wt_nat_le R
    unfold linObjectPadArg
    dsimp only [ctx] at *
    omega
  have hcell (i : Fin R) : (Val.list [ctx, .nat i]).wt ≤ linObjectPadArg W := by
    have hctx := wt_list2_le (encIntMatrix M) zero
    have ha := wt_list2_le ctx (.nat i)
    have hn := wt_nat_le i.val
    have := i.isLt
    unfold linObjectPadArg
    dsimp only [ctx] at *
    omega
  have ht := (linTabulate_spec h.tab ctx (fun i : Fin R => linVecVal (linObjectPadMatrix M R i))
    (100000 * (linObjectPadArg W + 1)) (fun i =>
      (linObjectPadCell_spec h.cell M i).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hcell i) 1)))).mono
    (linTabulateCost_mono harg hR le_rfl)
  have dc := Det.arg' (P := P) (vs := [ids, cols, encIntMatrix M]) (rest := []) (j := 1) rfl
  have dl := Det.length dc
  simp only [cols, encFun, List.length_map, List.length_finRange] at dl
  have dz : Det P [a] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have drow := Det.call (Det.mk2 dl dz) hz
  apply FunDet.intro h.entry
  apply EvalAll.letE drow
  intro v cv hv
  obtain ⟨rfl, hcv⟩ := hv
  have dm := Det.arg' (P := P) (vs := [ids, cols, encIntMatrix M])
    (rest := [zero]) (j := 2) rfl
  have di := Det.length (Det.arg' (P := P) (vs := [ids, cols, encIntMatrix M])
    (rest := [zero]) (j := 0) rfl)
  simp only [ids, encFun, List.length_map, List.length_finRange] at di
  have dzer := Det.var' (P := P) (env := [a, zero]) (i := 1) rfl
  have dout := Det.call (Det.mk2 (Det.mk2 dm dzer) di) ht
  refine dout.post fun cost hc => ⟨rfl, ?_⟩
  have wo := ht.wt_lt.le
  have hwctx := wt_list2_le (encIntMatrix M) zero
  have hwarg := wt_list2_le ctx (.nat R)
  have hnR := wt_nat_le R
  have hnd := wt_nat_le d
  have hwzero : (encInt 0).wt = 15 := by decide
  have hwrep := wt_list2_le (.nat d) (encInt 0)
  change _ ≤ linObjectPadCost W
  unfold linObjectPadCost
  dsimp only [a, W, cols, ids, ctx, zero, encFun, linObjectPadTabBudget] at *
  omega

theorem linObjectPadCost_poly : PBU (fun _ W _ => linObjectPadCost W) := by
  simp only [linObjectPadCost, linObjectPadZeroBudget, linObjectPadArg,
    linObjectPadTabBudget, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

theorem linObjectPadMatrix_relations {r d R : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (hR : r ≤ R) : linRelations (linObjectPadMatrix M R) = linRelations M := by
  simp only [linRelations, range_vecMulLinear]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < r
    · apply Submodule.subset_span
      refine ⟨⟨i.val, hi⟩, ?_⟩
      ext j
      simp [linObjectPadMatrix, hi]
    · have he : linObjectPadMatrix M R i = 0 := by ext j; simp [linObjectPadMatrix, hi]
      change linObjectPadMatrix M R i ∈ _
      rw [he]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Fin.castLE hR i, ?_⟩
    ext j
    simp [linObjectPadMatrix, i.isLt]

theorem linObjectPadMatrix_injective {r d R : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (hR : r ≤ R) (hM : Function.Injective M.mulVec) :
    Function.Injective (linObjectPadMatrix M R).mulVec := by
  intro x y hxy
  apply hM
  ext i
  have hi := congrFun hxy (Fin.castLE hR i)
  simpa [Matrix.mulVec, dotProduct, linObjectPadMatrix, i.isLt] using hi

end GI.Impl
