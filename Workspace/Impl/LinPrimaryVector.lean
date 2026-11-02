import Workspace.Impl.LinPrimaryDigit
import Workspace.Impl.LinPrimaryCoordinates
import Workspace.Impl.LinFinitePointMath
import Workspace.Impl.LinTabulate

/-! Read the first d primary digits of a full homogeneous point. The last
coordinate is omitted by using the length of the cyclic-order table. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryVectorCellF (digit : ℕ) : Expr :=
  .call digit (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (.get (arg 0) (.nat 2)) (arg 1)))
def linPrimaryVectorF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.length (arg 3)))
def linPrimaryVectorFuns (b : ℕ) : List Expr :=
  [linPrimaryVectorF (b + 2), linPrimaryVectorCellF (b + 9)] ++
    linTabulateFuns (b + 2) (b + 1) ++ linPrimaryDigitFuns (b + 9)

theorem linPrimaryVectorFuns_length (b : ℕ) : (linPrimaryVectorFuns b).length = 28 := rfl

structure linPrimaryVectorAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryVectorF (b + 2))
  cell : P.funs[b + 1]? = some (linPrimaryVectorCellF (b + 9))
  tab : linTabulateAt P (b + 2) (b + 1)
  digit : P.HasAt (b + 9) (linPrimaryDigitFuns (b + 9))

theorem linPrimaryVectorAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryVectorFuns b)) : linPrimaryVectorAt P b where
  entry := (h.block (gs := [linPrimaryVectorF (b + 2)]) 0 rfl).single
  cell := (h.block (gs := [linPrimaryVectorCellF (b + 9)]) 1 rfl).single
  tab := linTabulateAt_of (h.block 2 rfl)
  digit := h.block 9 rfl

def linPrimaryVectorCellCost (W : ℕ) : ℕ :=
  10000 * (W + linPrimaryDigitCost (100 * (W + 1)) + 1)
def linPrimaryVectorCost (W d : ℕ) : ℕ :=
  10000 * (W + d + linTabulateCost (100 * (W + d + 1)) d
    (linPrimaryVectorCellCost (100 * (W + d + 1))) + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linPrimaryVectorCell_spec {P : Program} {b p d : ℕ}
    (h : linPrimaryVectorAt P b) (hp : 0 < p) (q : ℕ) (x : Fin (d + 1) → ℕ)
    (ν : Fin d → ℕ) (i : Fin d) :
    FunDet P (b + 1)
      (.list [.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν], .nat i])
      (.nat ((x i.castSucc / q : ℕ) : ZMod p).val)
      (linPrimaryVectorCellCost
        (Val.list [.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν], .nat i]).wt) := by
  let ctx := Val.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν]
  let a := Val.list [ctx, .nat i]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.nat p).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wq : (Val.nat q).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wv : (linVecVal (fun k => (x k : ℤ))).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp [W, a])
  have wx : (encInt (x i.castSucc : ℤ)).wt < (linVecVal (fun k => (x k : ℤ))).wt :=
    wt_le_wt_list (List.mem_map.mpr ⟨i.castSucc, List.mem_finRange _, rfl⟩)
  have wa : (Val.list [.nat p, .nat q, encInt (x i.castSucc : ℤ)]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list3_le (.nat p) (.nat q) (encInt (x i.castSucc : ℤ))
    omega
  have hd := (linPrimaryDigit_spec h.digit hp q (x i.castSucc)).mono (linPrimaryDigitCost_mono wa)
  have dc := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have dp := Det.get' dc (Det.nat 0) rfl
  have dq := Det.get' dc (Det.nat 1) rfl
  have dv := Det.get' dc (Det.nat 2) rfl
  have di := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have dx := Det.get' dv di (v := encInt (x i.castSucc : ℤ)) (by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_finRange] using Nat.lt_succ_of_lt i.isLt)]
    simp
    rfl)
  apply FunDet.intro h.cell
  refine (Det.call (Det.mk3 dp dq dx) hd).mono ?_
  have wo := hd.wt_lt.le
  change _ ≤ linPrimaryVectorCellCost W
  unfold linPrimaryVectorCellCost
  dsimp only [a, W, ctx] at *
  omega

theorem linPrimaryVectorCellCost_mono {W V : ℕ} (h : W ≤ V) :
    linPrimaryVectorCellCost W ≤ linPrimaryVectorCellCost V := by
  unfold linPrimaryVectorCellCost linPrimaryDigitCost linIntCodecCost
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linPrimaryVector_spec {P : Program} {b p d : ℕ}
    (h : linPrimaryVectorAt P b) (hp : 0 < p) (q : ℕ) (x : Fin (d + 1) → ℕ) (ν : Fin d → ℕ) :
    FunDet P b (.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν])
      (encVec (fun i : Fin d => ((x i.castSucc / q : ℕ) : ZMod p)))
      (linPrimaryVectorCost (Val.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν]).wt d) := by
  let a := Val.list [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν]
  let W := a.wt
  have ww : (Val.list [a, .nat d]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat d)
    have hw := wt_nat_le d
    omega
  have wi (i : Fin d) : (Val.list [a, .nat i]).wt ≤ 100 * (W + d + 1) := by
    have hh := wt_list2_le a (.nat i)
    have hw := wt_nat_le i.val
    have := i.isLt
    omega
  have ht := linTabulate_spec h.tab a (fun i : Fin d => .nat ((x i.castSucc / q : ℕ) : ZMod p).val)
    (linPrimaryVectorCellCost (100 * (W + d + 1))) (fun i =>
      (linPrimaryVectorCell_spec h hp q x ν i).mono (linPrimaryVectorCellCost_mono (wi i)))
  have ht' := ht.mono (linTabulateCost_mono ww le_rfl le_rfl)
  have dn := Det.length (Det.arg' (P := P)
    (vs := [.nat p, .nat q, linVecVal (fun k => (x k : ℤ)), encFun ν]) (rest := []) (j := 3) rfl)
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl) dn) ht'
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have wd := wt_nat_le d
  have ww' := wt_list2_le a (.nat d)
  change _ ≤ linPrimaryVectorCost W d
  unfold linPrimaryVectorCost
  dsimp only [W, a, encFun, encVec] at *
  omega

theorem linPrimaryVectorCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linPrimaryVectorCost W d ≤ linPrimaryVectorCost V e := by
  simp only [linPrimaryVectorCost, linPrimaryVectorCellCost, linTabulateCost, linTabulateRangeCost,
    linMapBudget, linPrimaryDigitCost, linIntCodecCost]
  gcongr

theorem linPrimaryVectorCost_poly : PBU (fun d W _ => linPrimaryVectorCost W d) := by
  simp only [linPrimaryVectorCost, linPrimaryVectorCellCost, linTabulateCost, linTabulateRangeCost,
    linMapBudget, linPrimaryDigitCost, linIntCodecCost]
  norm_poly

end GI.Impl
