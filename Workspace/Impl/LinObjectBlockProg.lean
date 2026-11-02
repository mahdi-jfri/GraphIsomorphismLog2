import Workspace.Impl.LinObjectBlock
import Workspace.Impl.LinTabulate
import Workspace.Lang.Lib.LinIntTests
import Workspace.Lang.Lib.LinIntVector
import Workspace.Impl.AggStructDC

/-! A dense block-matrix assembler. The two explicit coordinate lists in
the input bound the dimensions even when there are no pieces or rows. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectBlockInput {p r d : ℕ} (M : Fin p → Matrix (Fin r) (Fin d) ℤ) : Val :=
  .list [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
    .list ((List.finRange p).map fun i => encIntMatrix (M i))]

def linObjectBlockCellF : Expr :=
  let input := .get (arg 0) (.nat 0)
  let row := .get (arg 0) (.nat 1)
  let col := arg 1
  let matrices := .get input (.nat 2)
  let p := .length matrices
  .ite (.arith .eq (.arith .mod row p) (.arith .mod col p))
    (.get (.get (.get matrices (.arith .mod row p)) (.arith .div row p))
      (.arith .div col p)) linIntZeroE

def linObjectBlockRowF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0)
    (.arith .mul (.length (.get (arg 0) (.nat 1)))
      (.length (.get (arg 0) (.nat 2)))))

def linObjectBlockF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0)
    (.arith .mul (.length (arg 0)) (.length (arg 2))))

def linObjectBlockFuns (b : ℕ) : List Expr :=
  [linObjectBlockF (b + 3), linObjectBlockRowF (b + 10), linObjectBlockCellF] ++
    linTabulateFuns (b + 3) (b + 1) ++ linTabulateFuns (b + 10) (b + 2)

theorem linObjectBlockFuns_length (b : ℕ) : (linObjectBlockFuns b).length = 17 := rfl

structure linObjectBlockAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectBlockF (b + 3))
  row : P.funs[b + 1]? = some (linObjectBlockRowF (b + 10))
  cell : P.funs[b + 2]? = some linObjectBlockCellF
  rows : linTabulateAt P (b + 3) (b + 1)
  cols : linTabulateAt P (b + 10) (b + 2)

theorem linObjectBlockAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linObjectBlockFuns b)) : linObjectBlockAt P b where
  entry := (h.block (gs := [linObjectBlockF (b + 3)]) 0 rfl).single
  row := (h.block (gs := [linObjectBlockRowF (b + 10)]) 1 rfl).single
  cell := (h.block (gs := [linObjectBlockCellF]) 2 rfl).single
  rows := linTabulateAt_of (h.block 3 rfl)
  cols := linTabulateAt_of (h.block 10 rfl)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linObjectBlockCell_spec {P : Program} {f p r d : ℕ}
    (hf : P.funs[f]? = some linObjectBlockCellF)
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (i k : Fin p) (a : Fin r) (j : Fin d) :
    let input := linObjectBlockInput M
    let row := (finProdFinEquiv (a, i)).val
    let col := (finProdFinEquiv (j, k)).val
    FunDet P f (.list [.list [input, .nat row], .nat col])
      (encInt (if i = k then M i a j else 0))
      (100000 * ((Val.list [.list [input, .nat row], .nat col]).wt + 1)) := by
  let input := linObjectBlockInput M
  let row := (finProdFinEquiv (a, i)).val
  let col := (finProdFinEquiv (j, k)).val
  let matrices := (List.finRange p).map fun i => encIntMatrix (M i)
  let ctx := Val.list [input, .nat row]
  let v := Val.list [ctx, .nat col]
  let W := v.wt
  let T := 100 * (W + 1)
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [v, W])
  have wcol : (Val.nat col).wt < W := wt_le_wt_list (by simp [v, W])
  have winput : input.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wrow : (Val.nat row).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wms : (Val.list matrices).wt < input.wt := wt_le_wt_list (by
    simp [input, linObjectBlockInput, matrices])
  have wmi : (encIntMatrix (M i)).wt < (Val.list matrices).wt := wt_le_wt_list (by
    simp [matrices])
  have wra : (linVecVal (M i a)).wt < (encIntMatrix (M i)).wt := wt_le_wt_list (by
    change linVecVal (M i a) ∈ (List.finRange r).map (fun a => linVecVal (M i a))
    exact List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩)
  have wcell := linVecEntryWt (M i a) j
  have hpW : p < W := by
    have hh := length_lt_wt_list matrices
    simp only [matrices, List.length_map, List.length_finRange] at hh
    change p < (Val.list matrices).wt at hh
    omega
  have hrW : r < W := by
    have hh := length_lt_wt_list ((List.finRange r).map fun i => Val.nat i.val)
    have hw : (encFun (fun i : Fin r => i.val)).wt < input.wt := wt_le_wt_list (by
      simp [input, linObjectBlockInput])
    simp only [List.length_map, List.length_finRange] at hh
    change r < (encFun (fun i : Fin r => i.val)).wt at hh
    omega
  have hdW : d < W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat i.val)
    have hw : (encFun (fun i : Fin d => i.val)).wt < input.wt := wt_le_wt_list (by
      simp [input, linObjectBlockInput])
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun (fun i : Fin d => i.val)).wt at hh
    omega
  have hT : W + 10 ≤ T := by dsimp [T]; omega
  have dc := StDC.arg (P := P) (vs := [ctx, .nat col]) (rest := []) (j := 0) rfl
    (show v.wt ≤ T by change W ≤ T; omega) (by omega) (show ctx.wt ≤ T by omega)
  have dj := StDC.arg (P := P) (vs := [ctx, .nat col]) (rest := []) (j := 1) rfl
    (show v.wt ≤ T by change W ≤ T; omega) (by omega) (show (Val.nat col).wt ≤ T by omega)
  have di := StDC.get dc (StDC.nat 0 (by omega)) rfl (show input.wt ≤ T by omega)
  have dr := StDC.get dc (StDC.nat 1 (by omega)) rfl (show (Val.nat row).wt ≤ T by omega)
  have dm := StDC.get di (StDC.nat 2 (by omega)) rfl
    (show (Val.list matrices).wt ≤ T by omega)
  have dp := StDC.length dm (by simp only [matrices, List.length_map, List.length_finRange]; omega)
  simp only [matrices, List.length_map, List.length_finRange] at dp
  have hmodr : GI.Machine.BinOp.mod.eval row p = i.val := by
    simp [GI.Machine.BinOp.eval, row, finProdFinEquiv, Nat.mod_eq_of_lt i.isLt]
  have hmodc : GI.Machine.BinOp.mod.eval col p = k.val := by
    simp [GI.Machine.BinOp.eval, col, finProdFinEquiv, Nat.mod_eq_of_lt k.isLt]
  have hdivr : GI.Machine.BinOp.div.eval row p = a.val := by
    simp [GI.Machine.BinOp.eval, row, finProdFinEquiv,
      Nat.add_mul_div_left _ _ (by omega : 0 < p), Nat.div_eq_of_lt i.isLt]
  have hdivc : GI.Machine.BinOp.div.eval col p = j.val := by
    simp [GI.Machine.BinOp.eval, col, finProdFinEquiv,
      Nat.add_mul_div_left _ _ (by omega : 0 < p), Nat.div_eq_of_lt k.isLt]
  have dmi := StDC.arith' dr dp hmodr (by have := i.isLt; omega)
  have dmk := StDC.arith' dj dp hmodc (by have := k.isLt; omega)
  have dra := StDC.arith' dr dp hdivr (by have := a.isLt; omega)
  have dcj := StDC.arith' dj dp hdivc (by have := j.isLt; omega)
  have dmat := StDC.get dm dmi (v := encIntMatrix (M i)) (by simp [matrices])
    (show (encIntMatrix (M i)).wt ≤ T by omega)
  have drow := StDC.get dmat dra (v := linVecVal (M i a)) (by simp [encIntMatrix, linVecVal])
    (show (linVecVal (M i a)).wt ≤ T by omega)
  have dent := StDC.get drow dcj (v := encInt (M i a j)) (by simp [linVecVal])
    (show (encInt (M i a j)).wt ≤ T by omega)
  have deq := StDC.arith dmi dmk (op := .eq) rfl (by
    simp only [GI.Machine.BinOp.eval]
    split_ifs
    · have hw : (Val.nat 1).wt = 3 := rfl
      rw [hw]; omega
    · have hw : (Val.nat 0).wt = 2 := rfl
      rw [hw]; omega)
  have dz : Det P [v] linIntZeroE (encInt 0) 100 := by
    exact (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have result := Det.ite' deq.det dent.det dz
  have he : (if GI.Machine.BinOp.eq.eval i.val k.val = 0 then encInt 0
      else encInt (M i a j)) = encInt (if i = k then M i a j else 0) := by
    by_cases hik : i = k
    · subst k; simp [GI.Machine.BinOp.eval]
    · have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
      simp [GI.Machine.BinOp.eval, hik, hval]
  rw [he] at result
  apply FunDet.intro hf
  exact result.mono (by
    change _ ≤ 100000 * (W + 1)
    have hz : (encInt 0).wt = 15 := by decide
    dsimp only [T]
    omega)

end GI.Impl
