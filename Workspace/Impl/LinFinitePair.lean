import Workspace.Impl.LinFiniteProduct
import Workspace.Impl.LinFiniteAction
import Workspace.Impl.LinIntSolverCost

/-! Multiplication and inversion of retained forward/inverse affine data. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linFinitePairVal {n : ℕ} (m : Fin n → ℤ) (A Ai : Matrix (Fin n) (Fin n) ℤ) : Val :=
  .list [linVecVal m, encIntMatrix A, encIntMatrix Ai]

def linFinitePairMulF (prod : ℕ) : Expr :=
  .letE (.call prod (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))
    (.letE (.call prod (mk3 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 2)) (.get (arg 0) (.nat 2))))
      (mk3 (.get (arg 0) (.nat 0)) (.var 1) (.var 2)))

def linFinitePairInvF : Expr := mk3 (arg 0) (arg 2) (arg 1)

def linFinitePairFuns (b : ℕ) : List Expr :=
  [linFinitePairMulF (b + 2), linFinitePairInvF] ++ linFiniteProductFuns (b + 2)

theorem linFinitePairFuns_length (b : ℕ) : (linFinitePairFuns b).length = 60 := rfl

structure linFinitePairAt (P : Program) (b : ℕ) : Prop where
  mul : P.funs[b]? = some (linFinitePairMulF (b + 2))
  inv : P.funs[b + 1]? = some linFinitePairInvF
  prod : linFiniteProductAt P (b + 2)

theorem linFinitePairAt_of {P : Program} {b : ℕ} (h : P.HasAt b (linFinitePairFuns b)) :
    linFinitePairAt P b where
  mul := (h.block (gs := [linFinitePairMulF (b + 2)]) 0 rfl).single
  inv := (h.block (gs := [linFinitePairInvF]) 1 rfl).single
  prod := linFiniteProductAt_of (h.block 2 rfl)

theorem linFiniteProductCost_mono {W V n : ℕ} (hW : W ≤ V) :
    linFiniteProductCost W n ≤ linFiniteProductCost V n := by
  have hm : linFiniteProductMulBudget W n ≤ linFiniteProductMulBudget V n :=
    linDenseMulCost_mono (by omega)
  have hr : linFiniteProductReduceBudget W n ≤ linFiniteProductReduceBudget V n :=
    linFiniteMatrixReduceCost_mono (by omega)
  unfold linFiniteProductCost
  omega

def linFinitePairMulCost (W n : ℕ) : ℕ :=
  100000 * (W + linFiniteProductCost (100 * (W + 1)) n + 1)
def linFinitePairInvCost (W : ℕ) : ℕ := 1000 * (W + 1)

theorem linFinitePairInv_spec {P : Program} {b n : ℕ} (hp : linFinitePairAt P b)
    (m : Fin n → ℤ) (A Ai : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P (b + 1) (linFinitePairVal m A Ai) (linFinitePairVal m Ai A)
      (linFinitePairInvCost (linFinitePairVal m A Ai).wt) := by
  have dm := Det.arg' (P := P) (vs := [linVecVal m, encIntMatrix A, encIntMatrix Ai]) (rest := []) (j := 0) rfl
  have dA := Det.arg' (P := P) (vs := [linVecVal m, encIntMatrix A, encIntMatrix Ai]) (rest := []) (j := 1) rfl
  have dAi := Det.arg' (P := P) (vs := [linVecVal m, encIntMatrix A, encIntMatrix Ai]) (rest := []) (j := 2) rfl
  have wm : (linVecVal m).wt < (linFinitePairVal m A Ai).wt := wt_le_wt_list (by simp [linFinitePairVal])
  have wA : (encIntMatrix A).wt < (linFinitePairVal m A Ai).wt := wt_le_wt_list (by simp [linFinitePairVal])
  have wAi : (encIntMatrix Ai).wt < (linFinitePairVal m A Ai).wt := wt_le_wt_list (by simp [linFinitePairVal])
  have wo := wt_list3_le (linVecVal m) (encIntMatrix Ai) (encIntMatrix A)
  apply FunDet.intro hp.inv
  refine (Det.mk3 dm dAi dA).mono ?_
  unfold linFinitePairInvCost
  dsimp only [linFinitePairVal] at *
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linFinitePairMul_spec {P : Program} {b n : ℕ} (hp : linFinitePairAt P b)
    (m : Fin n → ℤ) (A Ai B Bi : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P b (.list [linFinitePairVal m A Ai, linFinitePairVal m B Bi])
      (linFinitePairVal m (fun i j => (A * B) i j % m i) (fun i j => (Bi * Ai) i j % m i))
      (linFinitePairMulCost (Val.list [linFinitePairVal m A Ai, linFinitePairVal m B Bi]).wt n) := by
  let va := linFinitePairVal m A Ai
  let vb := linFinitePairVal m B Bi
  let a := Val.list [va, vb]
  let W := a.wt
  let C := linFiniteProductCost (100 * (W + 1)) n
  let F := encIntMatrix (fun i j => (A * B) i j % m i)
  let I := encIntMatrix (fun i j => (Bi * Ai) i j % m i)
  have wa : va.wt < W := wt_le_wt_list (by simp [W, a])
  have wb : vb.wt < W := wt_le_wt_list (by simp [W, a])
  have wm : (linVecVal m).wt < W :=
    (wt_le_wt_list (by simp [va, linFinitePairVal] : linVecVal m ∈ [linVecVal m, encIntMatrix A, encIntMatrix Ai])).trans wa
  have wA : (encIntMatrix A).wt < W := (wt_le_wt_list (by simp)).trans wa
  have wAi : (encIntMatrix Ai).wt < W := (wt_le_wt_list (by simp)).trans wa
  have wB : (encIntMatrix B).wt < W := (wt_le_wt_list (by simp)).trans wb
  have wBi : (encIntMatrix Bi).wt < W := (wt_le_wt_list (by simp)).trans wb
  have wi := wt_list3_le (linVecVal m) (encIntMatrix A) (encIntMatrix B)
  have wj := wt_list3_le (linVecVal m) (encIntMatrix Bi) (encIntMatrix Ai)
  have hwi : (Val.list [linVecVal m, encIntMatrix A, encIntMatrix B]).wt ≤ 100 * (W + 1) := by omega
  have hwj : (Val.list [linVecVal m, encIntMatrix Bi, encIntMatrix Ai]).wt ≤ 100 * (W + 1) := by omega
  have hf := (linFiniteProduct_spec hp.prod m A B).mono (linFiniteProductCost_mono hwi)
  have hi := (linFiniteProduct_spec hp.prod m Bi Ai).mono (linFiniteProductCost_mono hwj)
  have wf : F.wt ≤ C := hf.wt_lt.le
  have wI : I.wt ≤ C := hi.wt_lt.le
  have dout := wt_list3_le (linVecVal m) F I
  have da (k : ℕ) (rest : List Val) {v : Val} (hv : [va, vb][k]? = some v) :=
    Det.arg' (P := P) (vs := [va, vb]) (rest := rest) (j := k) hv
  have df := Det.call (Det.mk3
    (Det.get' (da 0 [] rfl) (Det.nat 0) rfl) (Det.get' (da 0 [] rfl) (Det.nat 1) rfl)
    (Det.get' (da 1 [] rfl) (Det.nat 1) rfl)) hf
  have di := Det.call (Det.mk3
    (Det.get' (da 0 [F] rfl) (Det.nat 0) rfl) (Det.get' (da 1 [F] rfl) (Det.nat 2) rfl)
    (Det.get' (da 0 [F] rfl) (Det.nat 2) rfl)) hi
  have dr := Det.mk3 (Det.get' (da 0 [F, I] rfl) (Det.nat 0) rfl)
    (Det.var' (P := P) (env := [a, F, I]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, F, I]) (i := 2) rfl)
  apply FunDet.intro hp.mul
  refine (Det.letE df (Det.letE di dr)).mono ?_
  unfold linFinitePairMulCost
  dsimp only [va, vb, a, W, C, F, I, linFinitePairVal, linVecVal, encIntMatrix] at *
  omega

theorem linFinitePairMulCost_mono {W V n : ℕ} (hW : W ≤ V) :
    linFinitePairMulCost W n ≤ linFinitePairMulCost V n := by
  have hh := linFiniteProductCost_mono (n := n) (show 100 * (W + 1) ≤ 100 * (V + 1) by omega)
  unfold linFinitePairMulCost
  omega

theorem linFinitePairMulCost_poly : PBU (fun n W _ => linFinitePairMulCost W n) := by
  have hp := linPoly_subst linFiniteProductCost_poly PBU.k (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add PBU.W hp) 1)

end GI.Impl
