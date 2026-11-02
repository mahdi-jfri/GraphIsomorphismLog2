import Workspace.Impl.LinIntAffineRows
import Workspace.Impl.LinFiniteHomogeneous

/-! Signed homogeneous matrices for the retained finite-abelian action. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linIntAffineMatrix_value {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (u : Fin d → ℤ) :
    encIntMatrix (linAffineMatrix A u) = .list
      (((List.finRange d).map fun i =>
        .list (((List.finRange d).map fun j => encInt (A i j)) ++ [encInt (u i)])) ++
        [.list (List.replicate d (encInt 0) ++ [encInt 1])]) := by
  have hrow (i : Fin d) : linVecVal (linExtend (A i) (u i)) =
      .list (((List.finRange d).map fun j => encInt (A i j)) ++ [encInt (u i)]) :=
    congrArg Val.list (linExtend_value encInt (A i) (u i))
  have hlast : linVecVal (linExtend (fun _ : Fin d => (0 : ℤ)) 1) =
      .list (List.replicate d (encInt 0) ++ [encInt 1]) := by
    simpa [linVecVal] using congrArg Val.list
      (linExtend_value encInt (fun _ : Fin d => (0 : ℤ)) 1)
  change Val.list ((List.finRange (d + 1)).map (fun i =>
    linVecVal (linExtend (fun i => linExtend (A i) (u i)) (linExtend (fun _ => 0) 1) i))) = _
  rw [linExtend_value]
  simp only [hrow, hlast]

def linIntAffineMatrixF (rows rep : ℕ) : Expr :=
  .letE (.call rows (.var 0))
    (.letE (.call rep (mk2 (.length (arg 1)) linIntZeroE))
      (.snoc (.var 1) (.snoc (.var 2) linIntOneE)))

def linIntAffineMatrixFuns (b : ℕ) : List Expr :=
  [linIntAffineMatrixF (b + 1) (b + 4)] ++ linAffineRowsFuns (b + 1) ++ replicateFuns (b + 4)

theorem linIntAffineMatrixFuns_length (b : ℕ) : (linIntAffineMatrixFuns b).length = 7 := rfl

structure linIntAffineMatrixAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linIntAffineMatrixF (b + 1) (b + 4))
  rows : P.HasAt (b + 1) (linAffineRowsFuns (b + 1))
  rep : P.HasAt (b + 4) (replicateFuns (b + 4))

theorem linIntAffineMatrixAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linIntAffineMatrixFuns b)) : linIntAffineMatrixAt P b where
  entry := (h.block (gs := [linIntAffineMatrixF (b + 1) (b + 4)]) 0 rfl).single
  rows := h.block 1 rfl
  rep := h.block 4 rfl

def linIntAffineMatrixCost (W d : ℕ) : ℕ :=
  10000 * (W + linAffineRowsCost W d + 1000000 * (W + d + 1) ^ 3 + d + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linIntAffineMatrix_spec {P : Program} {b d : ℕ} (h : linIntAffineMatrixAt P b)
    (A : Matrix (Fin d) (Fin d) ℤ) (u : Fin d → ℤ) :
    FunDet P b (.list [encIntMatrix A, linVecVal u]) (encIntMatrix (linAffineMatrix A u))
      (linIntAffineMatrixCost (Val.list [encIntMatrix A, linVecVal u]).wt d) := by
  let a := Val.list [encIntMatrix A, linVecVal u]
  let W := a.wt
  let rows := (List.finRange d).map fun i =>
    Val.list (((List.finRange d).map fun j => encInt (A i j)) ++ [encInt (u i)])
  let zs := List.replicate d (encInt 0)
  have hr := linIntAffineRows_spec h.rows A u
  have dr := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hr
  have rz := linReplicate_det h.rep d (encInt 0)
  have dl := Det.length (Det.arg' (P := P) (vs := [encIntMatrix A, linVecVal u])
    (rest := [.list rows]) (j := 1) rfl)
  simp only [linVecVal, List.length_map, List.length_finRange] at dl
  have dzero : Det P [a, .list rows] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have dz := Det.call (Det.mk2 dl dzero) rz
  have done : Det P [a, .list rows, .list zs] linIntOneE (encInt 1) 100 :=
    (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))).mono (by decide)
  have ds := Det.snoc (Det.var' (P := P) (env := [a, .list rows, .list zs]) (i := 1) rfl)
    (Det.snoc (Det.var' (P := P) (env := [a, .list rows, .list zs]) (i := 2) rfl) done)
  rw [linIntAffineMatrix_value]
  apply FunDet.intro h.entry
  refine (Det.letE dr (Det.letE dz ds)).mono ?_
  have wr := hr.wt_lt.le
  have wz : (Val.list zs).wt ≤ 100 * (d + 1) := by
    have hh := linWtList (vs := zs) (B := 15) (by intro v hv; rw [List.eq_of_mem_replicate hv]; decide)
    simp only [zs, List.length_replicate] at hh
    dsimp only [zs]
    omega
  have wlast := wt_list_snoc_le zs (encInt 1)
  have wout := wt_list_snoc_le rows (.list (zs ++ [encInt 1]))
  have w0 : (encInt 0).wt = 15 := rfl
  have w1 : (encInt 1).wt = 21 := rfl
  have wrep := wt_list2_le (.nat d) (encInt 0)
  have wi := wt_nat_le d
  have wu : (linVecVal u).wt < W := wt_le_wt_list (by simp [W, a])
  have hrep : loopModK * (d + 1) * ((Val.list [.nat d, encInt 0]).wt + d + (Val.list zs).wt + 1) ≤
      1000000 * (W + d + 1) ^ 3 := by
    simp only [loopModK]
    have hh : (Val.list [.nat d, encInt 0]).wt + d + (Val.list zs).wt + 1 ≤ 300 * (W + d + 1) := by omega
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega : d + 1 ≤ W + d + 1)) hh
    have hsq := Nat.pow_le_pow_right (by omega : 1 ≤ W + d + 1) (by decide : 2 ≤ 3)
    nlinarith only [hm, hsq]
  change _ ≤ linIntAffineMatrixCost W d
  unfold linIntAffineMatrixCost
  dsimp only [W, a, rows, zs, encIntMatrix, linVecVal] at *
  omega

theorem linIntAffineMatrixCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linIntAffineMatrixCost W d ≤ linIntAffineMatrixCost V e := by
  simp only [linIntAffineMatrixCost, linAffineRowsCost, linAffineRowsAcc, linVectorAccWt]
  gcongr

theorem linIntAffineMatrixCost_poly : PBU (fun d W _ => linIntAffineMatrixCost W d) := by
  unfold linIntAffineMatrixCost linAffineRowsCost linAffineRowsAcc linVectorAccWt
  norm_poly

end GI.Impl
