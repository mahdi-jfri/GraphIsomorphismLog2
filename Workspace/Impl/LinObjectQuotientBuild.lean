module

public import Workspace.Impl.LinObjectBlockSpec
public import Workspace.Impl.LinObjectDiagonalProg
public import Workspace.Impl.LinAppend

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectQuotientBuildF (block range diag app : ℕ) : Expr :=
  .letE (.call block (.var 0))
    (.letE (.call range (.arith .mul (.length (arg 1)) (.length (arg 2))))
      (.letE (.call diag (mk3 (arg 1) (.var 2) (.length (arg 2))))
        (.call app (mk2 (.var 1) (.var 3)))))

def linObjectQuotientBuildFuns (b : ℕ) : List Expr :=
  [linObjectQuotientBuildF (b + 1) (b + 38) (b + 18) (b + 35)] ++
    linObjectBlockFuns (b + 1) ++ linObjectDiagonalFuns (b + 18) ++
    appendFuns (b + 35) ++ rangeFuns (b + 38)

theorem linObjectQuotientBuildFuns_length (b : ℕ) :
    (linObjectQuotientBuildFuns b).length = 41 := rfl

structure linObjectQuotientBuildAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectQuotientBuildF (b + 1) (b + 38) (b + 18) (b + 35))
  block : linObjectBlockAt P (b + 1)
  diag : linObjectDiagonalAt P (b + 18)
  app : P.HasAt (b + 35) (appendFuns (b + 35))
  range : P.HasAt (b + 38) (rangeFuns (b + 38))

theorem linObjectQuotientBuildAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linObjectQuotientBuildFuns b)) : linObjectQuotientBuildAt P b where
  entry := (h.block (gs := [linObjectQuotientBuildF (b + 1) (b + 38) (b + 18) (b + 35)]) 0 rfl).single
  block := linObjectBlockAt_of (h.block 1 rfl)
  diag := linObjectDiagonalAt_of (h.block 18 rfl)
  app := h.block 35 rfl
  range := h.block 38 rfl

theorem linRange_spec {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (n : ℕ) :
    FunDet P b (.nat n) (encFun (fun i : Fin n => i.val)) (linTabulateRangeCost n) := by
  have hw := wt_ids_le n
  have hn := wt_nat_le n
  refine (range_spec h n).mono fun out cost ho => ⟨?_, ?_⟩
  · exact ho.1.trans range_eq_encPerm_one
  · have hc := ho.2
    rw [ho.1, range_eq_encPerm_one] at hc
    change cost ≤ loopModK * (n + 1) *
      ((Val.nat n).wt + n + (encFun (fun i : Fin n => i.val)).wt + 1) at hc
    unfold linTabulateRangeCost
    simp only [loopModK] at hc
    have hh : (Val.nat n).wt + n + (encFun (fun i : Fin n => i.val)).wt + 1 ≤
        10 * (4 * (n + 1) ^ 2 + n + 1) := by nlinarith
    exact hc.trans (by nlinarith [Nat.mul_le_mul_left (1000 * (n + 1)) hh])

def linObjectQuotientBuildBlockBudget (W : ℕ) : ℕ := linObjectBlockCost W (W * W) (W * W)
def linObjectQuotientBuildRangeBudget (W : ℕ) : ℕ := linTabulateRangeCost (W * W)
def linObjectQuotientBuildDiagArg (W : ℕ) : ℕ :=
  100 * (W + linObjectQuotientBuildRangeBudget W + 1)
def linObjectQuotientBuildDiagBudget (W : ℕ) : ℕ := linObjectDiagonalCost (linObjectQuotientBuildDiagArg W)
def linObjectQuotientBuildAppendArg (W : ℕ) : ℕ :=
  100 * (linObjectQuotientBuildBlockBudget W + linObjectQuotientBuildDiagBudget W + 1)
def linObjectQuotientBuildAppendBudget (W : ℕ) : ℕ := linAppendCost (linObjectQuotientBuildAppendArg W)
def linObjectQuotientBuildCost (W : ℕ) : ℕ :=
  10000000 * (W + linObjectQuotientBuildBlockBudget W + linObjectQuotientBuildRangeBudget W +
    linObjectQuotientBuildDiagBudget W + linObjectQuotientBuildAppendBudget W + 1)

theorem linObjectDiagonalCost_mono {W V : ℕ} (h : W ≤ V) :
    linObjectDiagonalCost W ≤ linObjectDiagonalCost V :=
  linMatrixTableCost_mono h h h (by omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linObjectQuotientBuild_spec {P : Program} {b p r d : ℕ}
    (h : linObjectQuotientBuildAt P b) (M : Fin p → Matrix (Fin r) (Fin d) ℤ) :
    FunDet P b (linObjectBlockInput M) (encIntMatrix (linObjectQuotientMatrix M))
      (linObjectQuotientBuildCost (linObjectBlockInput M).wt) := by
  let a := linObjectBlockInput M
  let W := a.wt
  let B := encIntMatrix (linObjectBlockMatrix M)
  let D := encIntMatrix (linObjectDiagonalMatrix p d)
  let ids := encFun (fun i : Fin (d * p) => i.val)
  let BB := linObjectQuotientBuildBlockBudget W
  let CB := linObjectQuotientBuildRangeBudget W
  let DB := linObjectQuotientBuildDiagBudget W
  let AB := linObjectQuotientBuildAppendBudget W
  obtain ⟨hr, hd, hp⟩ := linObjectBlockInput_dimensions M
  change r ≤ W at hr
  change d ≤ W at hd
  change p ≤ W at hp
  have hbm := (linObjectBlock_spec h.block M).mono
    (linObjectBlockCost_mono le_rfl (Nat.mul_le_mul hr hp) (Nat.mul_le_mul hd hp))
  have wB : B.wt ≤ BB := hbm.wt_lt.le
  have hrange := (linRange_spec h.range (d * p)).mono
    (show linTabulateRangeCost (d * p) ≤ CB from by
      dsimp only [CB, linObjectQuotientBuildRangeBudget, linTabulateRangeCost]
      gcongr
      all_goals exact Nat.mul_le_mul hd hp)
  have wids : ids.wt ≤ CB := hrange.wt_lt.le
  have hc : d * p ≤ CB := by
    have hh := length_lt_wt_list ((List.finRange (d * p)).map fun i => Val.nat i.val)
    simp only [List.length_map, List.length_finRange] at hh
    change d * p < ids.wt at hh
    omega
  have wd : (encFun (fun i : Fin d => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectBlockInput])
  have wm : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt < W :=
    wt_le_wt_list (by simp [a, W, linObjectBlockInput])
  have hdarg : (linObjectDiagonalInput p d).wt ≤ linObjectQuotientBuildDiagArg W := by
    have hh := wt_list3_le (encFun (fun i : Fin d => i.val)) ids (.nat p)
    have hpn := wt_nat_le p
    unfold linObjectDiagonalInput linObjectQuotientBuildDiagArg
    dsimp only [CB, ids, W, a] at *
    omega
  have hdiag := (linObjectDiagonal_spec h.diag).mono (linObjectDiagonalCost_mono hdarg)
  have wD : D.wt ≤ DB := hdiag.wt_lt.le
  have happ : (Val.list [B, D]).wt ≤ linObjectQuotientBuildAppendArg W := by
    have hh := wt_list2_le B D
    unfold linObjectQuotientBuildAppendArg
    dsimp only [BB, DB] at *
    omega
  have happf := (linAppend_spec h.app
    ((List.finRange (r * p)).map fun i => linVecVal (linObjectBlockMatrix M i))
    ((List.finRange d).map fun i => linVecVal (linObjectDiagonalMatrix p d i))).mono
    (show linAppendCost (Val.list [B, D]).wt ≤ AB from by
      change linAppendCost _ ≤ linAppendCost (linObjectQuotientBuildAppendArg W)
      unfold linAppendCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right happ 1) 2))
  have hb := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hbm
  have ddims := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [B]) (j := 1) rfl)
  have dpcs := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [B]) (j := 2) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at ddims dpcs
  have dr := Det.call (Det.arith' (op := .mul) ddims dpcs rfl) hrange
  have dhead := Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [B, ids]) (j := 1) rfl
  have dids := Det.var' (P := P) (env := [a, B, ids]) (i := 2) rfl
  have dpn := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [B, ids]) (j := 2) rfl)
  simp only [List.length_map, List.length_finRange] at dpn
  have dD := Det.call (Det.mk3 dhead dids dpn) hdiag
  have dB := Det.var' (P := P) (env := [a, B, ids, D]) (i := 1) rfl
  have dD' := Det.var' (P := P) (env := [a, B, ids, D]) (i := 3) rfl
  have dapp := Det.call (Det.mk2 dB dD') happf
  have result := Det.letE hb (Det.letE dr (Det.letE dD dapp))
  have he := linRowStack_value (linObjectBlockMatrix M) (linObjectDiagonalMatrix p d)
  rw [← he] at result
  apply FunDet.intro h.entry
  refine result.mono ?_
  have wout := happf.wt_lt.le
  rw [← he] at wout
  have wtapp := wt_list2_le B D
  have wtdiag := wt_list3_le (encFun (fun i : Fin d => i.val)) ids (.nat p)
  have hn := wt_nat_le (d * p)
  have hpn := wt_nat_le p
  change _ ≤ linObjectQuotientBuildCost W
  unfold linObjectQuotientBuildCost
  dsimp only [a, W, B, D, ids, BB, CB, DB, AB, linObjectBlockInput, encFun,
    GI.Machine.BinOp.eval, linObjectDiagonalInput, linObjectQuotientBuildBlockBudget,
    linObjectQuotientBuildRangeBudget, linObjectQuotientBuildDiagBudget,
    linObjectQuotientBuildAppendBudget] at *
  omega

theorem linObjectQuotientBuildCost_poly : PBU (fun _ W _ => linObjectQuotientBuildCost W) := by
  have hb : PBU (fun _ W _ => linObjectQuotientBuildBlockBudget W) :=
    linPoly_subst (f := fun r W c => linObjectBlockCost W r c) linObjectBlockCost_poly
      (PBU.mul PBU.W PBU.W) PBU.W (PBU.mul PBU.W PBU.W)
  have hr : PBU (fun _ W _ => linObjectQuotientBuildRangeBudget W) := by
    simp only [linObjectQuotientBuildRangeBudget, linTabulateRangeCost]
    norm_poly
  have ha : PBU (fun _ W _ => linObjectQuotientBuildDiagArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hr) 1)
  have hd : PBU (fun _ W _ => linObjectQuotientBuildDiagBudget W) :=
    linPoly_subst (f := fun _ W _ => linObjectDiagonalCost W)
      linObjectDiagonalCost_poly (PBU.const 0) ha (PBU.const 0)
  have haa : PBU (fun _ W _ => linObjectQuotientBuildAppendArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add hb hd) 1)
  have hab : PBU (fun _ W _ => linObjectQuotientBuildAppendBudget W) :=
    PBU.smul 100000 (PBU.pow (PBU.addc haa 1) 2)
  exact PBU.smul 10000000
    (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hb) hr) hd) hab) 1)

end GI.Impl
