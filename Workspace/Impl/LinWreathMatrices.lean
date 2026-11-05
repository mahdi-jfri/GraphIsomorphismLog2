module

public import Workspace.Impl.LinWreathMatrixItem
public import Workspace.Impl.LinZeroModMatrix
public import Workspace.Impl.LinListWeight
public import Workspace.Lang.Lib.LinIntTail

@[expose] public section

/-! Construct all dense generator images for one two-copy vector task. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linWreathMatricesF (map zero block append : ℕ) : Expr :=
  .letE (.call map (mk2 (.nat 0) (arg 0)))
    (.letE (.call map (mk2 (.nat 1) (arg 0)))
      (.letE (.call zero (arg 1))
        (.letE (.call block (mk2 (.var 3) (.nat 2)))
          (.letE (.call append (mk2 (.var 1) (.var 2))) (.snoc (.var 5) (.var 4))))))

def linWreathMatricesFuns (b : ℕ) : List Expr :=
  [linWreathMatricesF (b + 2) (b + 22) (b + 5) (b + 26), linWreathMatrixItemF (b + 5)] ++
    mapFuns (b + 2) (b + 1) ++ linWreathBlockFuns (b + 5) ++
    linZeroModMatrixFuns (b + 22) ++ appendFuns (b + 26)

theorem linWreathMatricesFuns_length (b : ℕ) : (linWreathMatricesFuns b).length = 29 := rfl

structure linWreathMatricesAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathMatricesF (b + 2) (b + 22) (b + 5) (b + 26))
  item : P.funs[b + 1]? = some (linWreathMatrixItemF (b + 5))
  map : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1))
  block : linWreathBlockAt P (b + 5)
  zero : P.HasAt (b + 22) (linZeroModMatrixFuns (b + 22))
  append : P.HasAt (b + 26) (appendFuns (b + 26))

theorem linWreathMatricesAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathMatricesFuns b)) : linWreathMatricesAt P b where
  entry := (h.block (gs := [linWreathMatricesF (b + 2) (b + 22) (b + 5) (b + 26)]) 0 rfl).single
  item := (h.block (gs := [linWreathMatrixItemF (b + 5)]) 1 rfl).single
  map := h.block 2 rfl
  block := linWreathBlockAt_of (h.block 5 rfl)
  zero := h.block 22 rfl
  append := h.block 26 rfl

/-- The order matches the two generator copies followed by the swap. -/
def linWreathMatrices {p d : ℕ} (hd : 0 < d)
    (As : List (Matrix (Fin d) (Fin d) (ZMod p))) : Val :=
  .list ((As.map fun A => encModMatrix (linWreathBlock hd A 0)) ++
    (As.map fun A => encModMatrix (linWreathBlock hd A 1)) ++
    [encModMatrix (linWreathBlock hd (0 : Matrix (Fin d) (Fin d) (ZMod p)) 2)])

def linWreathMatricesMapCost (W d : ℕ) : ℕ :=
  linMapBudget (100 * (W + 1)) (linWreathMatrixItemCost (100 * (W + 1)) d)
def linWreathMatricesSwapCost (d : ℕ) : ℕ :=
  linWreathBlockCost (100 * (linZeroModMatrixCost d + 1)) d
def linWreathMatricesAppendCost (W d : ℕ) : ℕ :=
  10000 * (W + 1) * (linWreathMatricesMapCost W d + W + 1)
def linWreathMatricesCost (W d : ℕ) : ℕ :=
  100000 * (W + linWreathMatricesMapCost W d + linZeroModMatrixCost d +
    linWreathMatricesSwapCost d + linWreathMatricesAppendCost W d + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linWreathMatrices_spec {P : Program} {b p d : ℕ} (h : linWreathMatricesAt P b)
    (hp : p.Prime) (hd : 0 < d) (As : List (Matrix (Fin d) (Fin d) (ZMod p))) :
    FunDet P b (.list [.list (As.map encModMatrix), .nat d]) (linWreathMatrices hd As)
      (linWreathMatricesCost (Val.list [.list (As.map encModMatrix), .nat d]).wt d) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let a := Val.list [.list (As.map encModMatrix), .nat d]
  let W := a.wt
  let ls := As.map (fun A => encModMatrix (linWreathBlock hd A 0))
  let rs := As.map (fun A => encModMatrix (linWreathBlock hd A 1))
  let z := encModMatrix (0 : Matrix (Fin d) (Fin d) (ZMod p))
  let s := encModMatrix (linWreathBlock hd (0 : Matrix (Fin d) (Fin d) (ZMod p)) 2)
  have wAs : (Val.list (As.map encModMatrix)).wt < W := wt_le_wt_list (by simp [W, a])
  have wd : (Val.nat d).wt < W := wt_le_wt_list (by simp [W, a])
  have len : As.length ≤ W := by
    have hh := length_lt_wt_list (As.map encModMatrix)
    simp only [List.length_map] at hh
    omega
  have warg (mode : Fin 3) : (Val.list [.nat mode, .list (As.map encModMatrix)]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat mode) (.list (As.map encModMatrix))
    have hw := wt_nat_le mode.val
    have := mode.isLt
    omega
  have wpoint (mode : Fin 3) (A : Matrix (Fin d) (Fin d) (ZMod p)) (hA : A ∈ As) :
      (Val.list [.nat mode, encModMatrix A]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat mode) (encModMatrix A)
    have hw : (encModMatrix A).wt < (Val.list (As.map encModMatrix)).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨A, hA, rfl⟩)
    have hn := wt_nat_le mode.val
    have := mode.isLt
    omega
  have hmap (mode : Fin 3) := linMapEncoded_spec h.map encModMatrix encModMatrix_injective
    (fun A => encModMatrix (linWreathBlock hd A mode)) (.nat mode) As
    (linWreathMatrixItemCost (100 * (W + 1)) d) (fun A hA =>
      (linWreathMatrixItem_spec h.item h.block hp hd A mode).mono
        (linWreathMatrixItemCost_mono (wpoint mode A hA) le_rfl))
  have hl : FunDet P (b + 2) (.list [.nat 0, .list (As.map encModMatrix)]) (.list ls)
      (linWreathMatricesMapCost W d) :=
    (hmap (0 : Fin 3)).mono (linMapBudget_mono (warg 0) le_rfl)
  have hr : FunDet P (b + 2) (.list [.nat 1, .list (As.map encModMatrix)]) (.list rs)
      (linWreathMatricesMapCost W d) :=
    (hmap (1 : Fin 3)).mono (linMapBudget_mono (warg 1) le_rfl)
  have wl := hl.wt_lt.le
  have wr := hr.wt_lt.le
  have wp := linListAppendWt ls rs
  have wi := wt_list2_le (.list ls) (.list rs)
  have hap := linAppend_det h.append ls rs
  have hap' := hap.mono (c' := linWreathMatricesAppendCost W d) (by
    have hlen : rs.length = As.length := by simp [rs]
    rw [hlen]
    unfold linWreathMatricesAppendCost
    simp only [loopModK]
    have hw : (Val.list [.list ls, .list rs]).wt + As.length + (Val.list (ls ++ rs)).wt + 1 ≤
        10 * (linWreathMatricesMapCost W d + W + 1) := by omega
    exact (Nat.mul_le_mul (by omega : 1000 * (As.length + 1) ≤ 1000 * (W + 1)) hw).trans (by ring_nf; omega))
  have hz := linZeroModMatrix_spec h.zero p d
  have wz := hz.wt_lt.le
  have wis := wt_list2_le z (.nat 2)
  have wb : (Val.list [z, .nat 2]).wt ≤ 100 * (linZeroModMatrixCost d + 1) := by
    have wn : (Val.nat 2).wt = 4 := rfl
    change z.wt ≤ linZeroModMatrixCost d at wz
    omega
  have hs := (linWreathBlock_spec h.block hp hd (0 : Matrix (Fin d) (Fin d) (ZMod p)) (2 : Fin 3)).mono
    (linWreathBlockCost_mono wb le_rfl)
  change FunDet P (b + 5) (.list [z, .nat 2]) s (linWreathMatricesSwapCost d) at hs
  have ws := hs.wt_lt.le
  have dAs := Det.arg' (P := P) (vs := [.list (As.map encModMatrix), .nat d]) (rest := []) (j := 0) rfl
  have dl := Det.call (Det.mk2 (Det.nat 0) dAs) hl
  have dAs' := Det.arg' (P := P) (vs := [.list (As.map encModMatrix), .nat d]) (rest := [.list ls]) (j := 0) rfl
  have dr := Det.call (Det.mk2 (Det.nat 1) dAs') hr
  have dz := Det.call (Det.arg' (P := P) (vs := [.list (As.map encModMatrix), .nat d])
    (rest := [.list ls, .list rs]) (j := 1) rfl) hz
  have ds := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, .list ls, .list rs, z]) (i := 3) rfl) (Det.nat 2)) hs
  have dap := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, .list ls, .list rs, z, s]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, .list ls, .list rs, z, s]) (i := 2) rfl)) hap'
  have dout := Det.snoc
    (Det.var' (P := P) (env := [a, .list ls, .list rs, z, s, .list (ls ++ rs)]) (i := 5) rfl)
    (Det.var' (P := P) (env := [a, .list ls, .list rs, z, s, .list (ls ++ rs)]) (i := 4) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dl (Det.letE dr (Det.letE dz (Det.letE ds (Det.letE dap dout))))).mono ?_
  have wo := wt_list_snoc_le (ls ++ rs) s
  have wm0 := wt_list2_le (.nat 0) (.list (As.map encModMatrix))
  have wm1 := wt_list2_le (.nat 1) (.list (As.map encModMatrix))
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  have w2 : (Val.nat 2).wt = 4 := rfl
  change _ ≤ linWreathMatricesCost W d
  dsimp only [linWreathMatricesCost]
  change s.wt ≤ linWreathMatricesSwapCost d at ws
  dsimp only [a, W, z, s, ls, rs, linWreathMatricesSwapCost] at *
  norm_num only [Fin.val_ofNat, Nat.reduceMod] at *
  omega

theorem linWreathMatricesCost_poly : PBU (fun d W _ => linWreathMatricesCost W d) := by
  simp only [linWreathMatricesCost, linWreathMatricesAppendCost, linWreathMatricesMapCost,
    linWreathMatricesSwapCost, linZeroModMatrixCost, linWreathMatrixItemCost,
    linWreathBlockCost, linWreathBlockRowCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
