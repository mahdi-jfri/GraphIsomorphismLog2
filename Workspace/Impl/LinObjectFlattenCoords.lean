module

public import Workspace.Impl.LinObjectVectorRow

@[expose] public section

/-! Convert the matrix of local coordinate rows into the interleaved
vector used by the integer presentation. Both dimension headers are explicit. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectCoordsInput {p d : ℕ} (M : Matrix (Fin p) (Fin d) ℤ) : Val :=
  .list [encFun (fun i : Fin p => i.val), encFun (fun j : Fin d => j.val), encIntMatrix M]

def linObjectFlattenCoordsCellF : Expr :=
  let p := .length (.get (arg 0) (.nat 0))
  .get (.get (.get (arg 0) (.nat 2)) (.arith .mod (arg 1) p)) (.arith .div (arg 1) p)

def linObjectFlattenCoordsF (tab : ℕ) : Expr :=
  .call tab (mk2 (.var 0) (.arith .mul (.length (arg 1)) (.length (arg 0))))

def linObjectFlattenCoordsFuns (b : ℕ) : List Expr :=
  [linObjectFlattenCoordsF (b + 2), linObjectFlattenCoordsCellF] ++ linTabulateFuns (b + 2) (b + 1)

theorem linObjectFlattenCoordsFuns_length (b : ℕ) : (linObjectFlattenCoordsFuns b).length = 9 := rfl

theorem linObjectCoordsInput_dims {p d : ℕ} (M : Matrix (Fin p) (Fin d) ℤ) :
    p ≤ (linObjectCoordsInput M).wt ∧ d ≤ (linObjectCoordsInput M).wt := by
  have hp := length_lt_wt_list ((List.finRange p).map fun i => Val.nat i.val)
  have hd := length_lt_wt_list ((List.finRange d).map fun i => Val.nat i.val)
  have wp : (encFun (fun i : Fin p => i.val)).wt < (linObjectCoordsInput M).wt :=
    wt_le_wt_list (by simp [linObjectCoordsInput])
  have wd : (encFun (fun i : Fin d => i.val)).wt < (linObjectCoordsInput M).wt :=
    wt_le_wt_list (by simp [linObjectCoordsInput])
  simp only [List.length_map, List.length_finRange] at hp hd
  change p < (encFun (fun i : Fin p => i.val)).wt at hp
  change d < (encFun (fun i : Fin d => i.val)).wt at hd
  constructor <;> omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectFlattenCoordsCell_spec {P : Program} {f p d : ℕ}
    (hf : P.funs[f]? = some linObjectFlattenCoordsCellF) (M : Matrix (Fin p) (Fin d) ℤ)
    (i : Fin p) (j : Fin d) :
    let k := finProdFinEquiv (j, i)
    let a := Val.list [linObjectCoordsInput M, .nat k]
    FunDet P f a (encInt (M i j)) (100000 * (a.wt + 1)) := by
  let k := finProdFinEquiv (j, i)
  let ctx := linObjectCoordsInput M
  let a := Val.list [ctx, .nat k]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  obtain ⟨hp, hd⟩ := linObjectCoordsInput_dims M
  have wp : (encFun (fun i : Fin p => i.val)).wt < ctx.wt :=
    wt_le_wt_list (by simp [ctx, linObjectCoordsInput])
  have wm : (encIntMatrix M).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linObjectCoordsInput])
  have wr : (linVecVal (M i)).wt < (encIntMatrix M).wt := wt_le_wt_list (by
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  have wcell := linVecEntryWt (M i) j
  have hii := i.isLt
  have hjj := j.isLt
  have dc := Det.arg' (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 0) rfl
  have dk := Det.arg' (P := P) (vs := [ctx, .nat k]) (rest := []) (j := 1) rfl
  have dm := Det.get' dc (Det.nat 2) rfl
  have dp := Det.length (Det.get' dc (Det.nat 0) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at dp
  have hm : GI.Machine.BinOp.mod.eval k.val p = i.val := by
    simp [GI.Machine.BinOp.eval, k, finProdFinEquiv, Nat.mod_eq_of_lt i.isLt]
  have hv : GI.Machine.BinOp.div.eval k.val p = j.val := by
    simp [GI.Machine.BinOp.eval, k, finProdFinEquiv,
      Nat.add_mul_div_left _ _ (by omega : 0 < p), Nat.div_eq_of_lt i.isLt]
  have di := Det.arith' dk dp hm
  have dj := Det.arith' dk dp hv
  have dr := Det.get' dm di (v := linVecVal (M i)) (by simp [encIntMatrix, linVecVal])
  have dout := Det.get' dr dj (v := encInt (M i j)) (by simp [linVecVal])
  apply FunAll.intro hf
  refine dout.post fun cost hc => ⟨rfl, ?_⟩
  dsimp only [ctx, a, W, k, linObjectCoordsInput, encFun] at *
  omega

def linObjectFlattenCoordsArg (W : ℕ) : ℕ := 100 * (W + 1) ^ 2
def linObjectFlattenCoordsBudget (W : ℕ) : ℕ :=
  linTabulateCost (linObjectFlattenCoordsArg W) (W * W) (100000 * (linObjectFlattenCoordsArg W + 1))
def linObjectFlattenCoordsCost (W : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + linObjectFlattenCoordsBudget W + 1)

theorem linObjectFlattenCoordsCost_poly : PBU (fun _ W _ => linObjectFlattenCoordsCost W) := by
  unfold linObjectFlattenCoordsCost linObjectFlattenCoordsBudget linObjectFlattenCoordsArg
    linTabulateCost linTabulateRangeCost linMapBudget
  norm_poly

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectFlattenCoords_spec {P : Program} {b p d : ℕ}
    (h : P.HasAt b (linObjectFlattenCoordsFuns b)) (M : Matrix (Fin p) (Fin d) ℤ) :
    FunDet P b (linObjectCoordsInput M)
      (linVecVal ((linObjectUnflatten p d).symm M)) (linObjectFlattenCoordsCost (linObjectCoordsInput M).wt) := by
  let a := linObjectCoordsInput M
  let W := a.wt
  obtain ⟨hp, hd⟩ := linObjectCoordsInput_dims M
  have hn : d * p ≤ W * W := Nat.mul_le_mul hd hp
  have hc := (h.block (gs := [linObjectFlattenCoordsCellF]) 1 rfl).single
  have hs := linTabulate_spec (linTabulateAt_of (h.block 2 rfl)) a
    (fun k : Fin (d * p) => encInt (((linObjectUnflatten p d).symm M) k))
    (100000 * (linObjectFlattenCoordsArg W + 1)) (fun k => by
      let i := (finProdFinEquiv.symm k).2
      let j := (finProdFinEquiv.symm k).1
      have hh := linObjectFlattenCoordsCell_spec hc M i j
      have hk : finProdFinEquiv (j, i) = k := finProdFinEquiv.apply_symm_apply k
      simp only [hk] at hh
      exact hh.mono (by
        have ha := wt_list2_le a (.nat k)
        have hw := wt_nat_le k.val
        have hkn := k.isLt
        unfold linObjectFlattenCoordsArg
        dsimp only [W] at *
        nlinarith))
  have ha : (Val.list [a, .nat (d * p)]).wt ≤ linObjectFlattenCoordsArg W := by
    have hh := wt_list2_le a (.nat (d * p))
    have hw := wt_nat_le (d * p)
    unfold linObjectFlattenCoordsArg
    nlinarith
  have hs' := hs.mono (linTabulateCost_mono ha hn le_rfl)
  have dd := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin p => i.val), encFun (fun i : Fin d => i.val), encIntMatrix M])
    (rest := []) (j := 1) rfl)
  have dp := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin p => i.val), encFun (fun i : Fin d => i.val), encIntMatrix M])
    (rest := []) (j := 0) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at dd dp
  have dn := Det.arith' (op := .mul) dd dp (z := d * p) rfl
  have df := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl) dn) hs'
  apply FunAll.intro (h.block (gs := [linObjectFlattenCoordsF (b + 2)]) 0 rfl).single
  refine df.post fun cost hc => ⟨rfl, ?_⟩
  have wo := hs'.wt_lt.le
  have hh := wt_list2_le a (.nat (d * p))
  have hw := wt_nat_le (d * p)
  have wd : (encFun (fun i : Fin d => i.val)).wt < W :=
    wt_le_wt_list (by simp [a, W, linObjectCoordsInput])
  have wp : (encFun (fun i : Fin p => i.val)).wt < W :=
    wt_le_wt_list (by simp [a, W, linObjectCoordsInput])
  change cost ≤ linObjectFlattenCoordsCost W
  unfold linObjectFlattenCoordsCost
  dsimp only [a, W, linObjectCoordsInput, encFun, linObjectFlattenCoordsBudget] at *
  nlinarith

end GI.Impl
