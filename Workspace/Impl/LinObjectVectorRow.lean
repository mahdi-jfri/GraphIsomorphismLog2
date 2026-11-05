module

public import Workspace.Impl.LinObjectBlockPresentation
public import Workspace.Impl.LinObjectBlockSpec

@[expose] public section

/-! Extract one local vector from the interleaved coordinates used by
the block presentation. The order is piece + p * coordinate. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectVectorRowCellF : Expr :=
  .get (.get (arg 0) (.nat 3))
    (.arith .add (.get (arg 0) (.nat 2))
      (.arith .mul (.get (arg 0) (.nat 0)) (arg 1)))

def linObjectVectorRowF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (arg 1))

def linObjectVectorRowFuns (b : ℕ) : List Expr :=
  [linObjectVectorRowF (b + 2), linObjectVectorRowCellF] ++ linTabulateFuns (b + 2) (b + 1)

theorem linObjectVectorRowFuns_length (b : ℕ) : (linObjectVectorRowFuns b).length = 9 := rfl

def linObjectVectorRowCellCost (W : ℕ) : ℕ := 100000 * (W + 1)
def linObjectVectorRowBudget (W : ℕ) : ℕ :=
  linTabulateCost (100 * (W + 1)) W (linObjectVectorRowCellCost (100 * (W + 1)))
def linObjectVectorRowCost (W : ℕ) : ℕ := 100000 * (W + linObjectVectorRowBudget W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectVectorRowCell_spec {P : Program} {f p d : ℕ}
    (hf : P.funs[f]? = some linObjectVectorRowCellF) (z : Fin (d * p) → ℤ)
    (i : Fin p) (j : Fin d) :
    let a := Val.list [.list [.nat p, .nat d, .nat i, linVecVal z], .nat j]
    FunDet P f a (encInt (linObjectUnflatten p d z i j)) (linObjectVectorRowCellCost a.wt) := by
  let ctx := Val.list [.nat p, .nat d, .nat i, linVecVal z]
  let a := Val.list [ctx, .nat j]
  let W := a.wt
  let k := finProdFinEquiv (j, i)
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wj : (Val.nat j).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wi : (Val.nat i).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wz : (linVecVal z).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have hk : k.val < d * p := k.isLt
  have hdim : d * p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (d * p)).map fun i => encInt (z i))
    simp only [List.length_map, List.length_finRange] at hh
    change d * p < (linVecVal z).wt at hh
    omega
  have wout := linVecEntryWt z k
  have dc := Det.arg' (P := P) (vs := [ctx, .nat j]) (rest := []) (j := 0) rfl
  have dj := Det.arg' (P := P) (vs := [ctx, .nat j]) (rest := []) (j := 1) rfl
  have dp := Det.get' dc (Det.nat 0) rfl
  have di := Det.get' dc (Det.nat 2) rfl
  have dz := Det.get' dc (Det.nat 3) rfl
  have dm := Det.arith' (op := .mul) dp dj (z := p * j.val) rfl
  have da := Det.arith' (op := .add) di dm (z := k.val) rfl
  have dout := Det.get' dz da (v := encInt (z k)) (by simp [linVecVal])
  apply FunAll.intro hf
  refine dout.post fun cost hc => ⟨rfl, ?_⟩
  have hprod : p * j.val ≤ k.val := by change p * j.val ≤ i.val + p * j.val; omega
  have hi : i.val ≤ k.val := by change i.val ≤ i.val + p * j.val; omega
  unfold linObjectVectorRowCellCost
  dsimp only [ctx, a, W] at *
  omega

theorem linObjectVectorRowBudget_poly : PBU (fun _ W _ => linObjectVectorRowBudget W) := by
  unfold linObjectVectorRowBudget linObjectVectorRowCellCost linTabulateCost linTabulateRangeCost linMapBudget
  norm_poly

theorem linObjectVectorRowCost_poly : PBU (fun _ W _ => linObjectVectorRowCost W) :=
  PBU.smul 100000 (PBU.addc (PBU.add PBU.W linObjectVectorRowBudget_poly) 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectVectorRow_spec {P : Program} {b p d : ℕ}
    (h : P.HasAt b (linObjectVectorRowFuns b)) (z : Fin (d * p) → ℤ) (i : Fin p) :
    let a := Val.list [.nat p, .nat d, .nat i, linVecVal z]
    FunDet P b a (linVecVal (linObjectUnflatten p d z i)) (linObjectVectorRowCost a.wt) := by
  let a := Val.list [.nat p, .nat d, .nat i, linVecVal z]
  let W := a.wt
  have wz : (linVecVal z).wt < W := wt_le_wt_list (by simp [a, W])
  have wd : (Val.nat d).wt < W := wt_le_wt_list (by simp [a, W])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (d * p)).map fun i => encInt (z i))
    simp only [List.length_map, List.length_finRange] at hh
    change d * p < (linVecVal z).wt at hh
    have hp : 0 < p := Nat.zero_lt_of_lt i.isLt
    have hdp : d ≤ d * p := Nat.le_mul_of_pos_right d hp
    omega
  have hc := (h.block (gs := [linObjectVectorRowCellF]) 1 rfl).single
  have hs := linTabulate_spec (linTabulateAt_of (h.block 2 rfl)) a
    (fun j : Fin d => encInt (linObjectUnflatten p d z i j))
    (linObjectVectorRowCellCost (100 * (W + 1))) (fun j =>
      (linObjectVectorRowCell_spec hc z i j).mono (by
        have hh := wt_list2_le a (.nat j)
        have hj := wt_nat_le j.val
        have hjd := j.isLt
        unfold linObjectVectorRowCellCost
        dsimp only [a, W] at *
        omega))
  have harg : (Val.list [a, .nat d]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le a (.nat d)
    omega
  have hb : linTabulateCost (Val.list [a, .nat d]).wt d
      (linObjectVectorRowCellCost (100 * (W + 1))) ≤ linObjectVectorRowBudget W :=
    linTabulateCost_mono harg hd le_rfl
  have df := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    (Det.arg' (P := P) (vs := [.nat p, .nat d, .nat i, linVecVal z]) (rest := []) (j := 1) rfl))
    (hs.mono hb)
  apply FunAll.intro (h.block (gs := [linObjectVectorRowF (b + 2)]) 0 rfl).single
  refine df.post fun cost hc => ⟨rfl, ?_⟩
  have wo := (hs.mono hb).wt_lt.le
  have hh := wt_list2_le a (.nat d)
  change cost ≤ linObjectVectorRowCost W
  unfold linObjectVectorRowCost
  dsimp only [a, W] at *
  omega

end GI.Impl
