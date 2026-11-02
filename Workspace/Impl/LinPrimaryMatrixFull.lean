import Workspace.Impl.LinPrimaryMatrixProg
import Workspace.Impl.LinFiniteActionCost

/-! Build a primary field-layer matrix directly from the retained signed
integer full-action record. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linModMatrix_dense_spec {P : Program} {b p n : ℕ}
    (h : P.HasAt b (linModMatrixFuns b)) (hp : 0 < p)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P b (.list [.nat p, encIntMatrix A])
      (encModMatrix (fun i k => (A i k : ZMod p)))
      (linModMatrixCost (Val.list [.nat p, encIntMatrix A]).wt) := by
  have hh := linModMatrix_spec h hp ((List.finRange n).map fun i => (List.finRange n).map (A i))
  simpa only [encIntMatrix, encModMatrix, encVec, List.map_map, Function.comp_def] using hh

theorem linModMatrixCost_mono {W V : ℕ} (h : W ≤ V) : linModMatrixCost W ≤ linModMatrixCost V := by
  simp only [linModMatrixCost, linModVectorCost, linMapBudget, linModReduceCost, linIntCodecCost]
  gcongr

def linPrimaryMatrixFullF (mod matrix : ℕ) : Expr :=
  .letE (.call mod (mk2 (arg 1) (.get (arg 0) (.nat 1))))
    (.call matrix (mk3 (.var 1) (arg 2) (arg 3)))

def linPrimaryMatrixFullFuns (b : ℕ) : List Expr :=
  [linPrimaryMatrixFullF (b + 1) (b + 26)] ++ linModMatrixFuns (b + 1) ++ linPrimaryMatrixFuns (b + 26)

theorem linPrimaryMatrixFullFuns_length (b : ℕ) : (linPrimaryMatrixFullFuns b).length = 43 := rfl

structure linPrimaryMatrixFullAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryMatrixFullF (b + 1) (b + 26))
  mod : P.HasAt (b + 1) (linModMatrixFuns (b + 1))
  matrix : linPrimaryMatrixAt P (b + 26)

theorem linPrimaryMatrixFullAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryMatrixFullFuns b)) : linPrimaryMatrixFullAt P b where
  entry := (h.block (gs := [linPrimaryMatrixFullF (b + 1) (b + 26)]) 0 rfl).single
  mod := h.block 1 rfl
  matrix := linPrimaryMatrixAt_of (h.block 26 rfl)

def linPrimaryMatrixFullModBudget (W : ℕ) : ℕ := linModMatrixCost (100 * (W + 1))
def linPrimaryMatrixFullArg (W : ℕ) : ℕ := 100 * (W + linPrimaryMatrixFullModBudget W + 1)
def linPrimaryMatrixFullBuildBudget (W : ℕ) : ℕ := linPrimaryMatrixCost (linPrimaryMatrixFullArg W) W

def linPrimaryMatrixFullCost (W : ℕ) : ℕ :=
  100000 * (W + linPrimaryMatrixFullModBudget W + linPrimaryMatrixFullBuildBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 6000 in
theorem linPrimaryMatrixFull_spec {P : Program} {b p d : ℕ} (h : linPrimaryMatrixFullAt P b)
    (hp : p.Prime) (ν : Fin d → ℕ) (level : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (u : linFiniteVec (linPrimaryOrders p ν)) (inv : Val) :
    let m := linPrimaryOrders p ν
    let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
    let a := Val.list [record, .nat p, encFun ν, .nat level]
    FunDet P b a (encModMatrix (linPrimaryFieldMatrix p ν level f)) (linPrimaryMatrixFullCost a.wt) := by
  let m := linPrimaryOrders p ν
  let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
  let a := Val.list [record, .nat p, encFun ν, .nat level]
  let W := a.wt
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) (ZMod p) := fun i k => (linFiniteHomogeneous m f u i k : ZMod p)
  have wrec : record.wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W, a])
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have wl : (Val.nat level).wt < W := wt_le_wt_list (by simp [W, a])
  have wmat : (encIntMatrix (linFiniteHomogeneous m f u)).wt < record.wt := wt_le_wt_list (by simp [record])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have warg : (Val.list [.nat p, encIntMatrix (linFiniteHomogeneous m f u)]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat p) (encIntMatrix (linFiniteHomogeneous m f u))
    omega
  have hm : FunDet P (b + 1) (.list [.nat p, encIntMatrix (linFiniteHomogeneous m f u)])
      (encModMatrix A) (linPrimaryMatrixFullModBudget W) :=
    (linModMatrix_dense_spec h.mod hp.pos (linFiniteHomogeneous m f u)).mono (linModMatrixCost_mono warg)
  have wA := hm.wt_lt.le
  have wbuild : (Val.list [encModMatrix A, encFun ν, .nat level]).wt ≤ linPrimaryMatrixFullArg W := by
    have hh := wt_list3_le (encModMatrix A) (encFun ν) (.nat level)
    unfold linPrimaryMatrixFullArg
    omega
  have hb := (linPrimaryMatrix_spec h.matrix hp A ν level).mono (linPrimaryMatrixCost_mono wbuild hd)
  have he : A.submatrix Fin.castSucc Fin.castSucc =
      (fun i k => (linFiniteMatrix m f i k : ZMod p)) := by
    funext i k
    simp only [A, Matrix.submatrix_apply, linFiniteHomogeneous, linAffineMatrix,
      linExtend_castSucc, linFiniteIntMatrix, Int.cast_natCast]
  rw [he] at hb
  change FunDet P (b + 26) (.list [encModMatrix A, encFun ν, .nat level])
    (encModMatrix (linPrimaryFieldMatrix p ν level f)) (linPrimaryMatrixFullBuildBudget W) at hb
  have wo := hb.wt_lt.le
  have dr := Det.arg' (P := P) (vs := [record, .nat p, encFun ν, .nat level]) (rest := []) (j := 0) rfl
  have dp := Det.arg' (P := P) (vs := [record, .nat p, encFun ν, .nat level]) (rest := []) (j := 1) rfl
  have dm := Det.get' dr (Det.nat 1) rfl
  have dmod := Det.call (Det.mk2 dp dm) hm
  have dν := Det.arg' (P := P) (vs := [record, .nat p, encFun ν, .nat level]) (rest := [encModMatrix A]) (j := 2) rfl
  have dl := Det.arg' (P := P) (vs := [record, .nat p, encFun ν, .nat level]) (rest := [encModMatrix A]) (j := 3) rfl
  have dbuild := Det.call (Det.mk3
    (Det.var' (P := P) (env := [a, encModMatrix A]) (i := 1) rfl) dν dl) hb
  apply FunDet.intro h.entry
  refine (Det.letE dmod dbuild).mono ?_
  have wi := wt_list2_le (.nat p) (encIntMatrix (linFiniteHomogeneous m f u))
  have wb := wt_list3_le (encModMatrix A) (encFun ν) (.nat level)
  change _ ≤ linPrimaryMatrixFullCost W
  dsimp only [linPrimaryMatrixFullCost]
  dsimp only [a, W, record, A] at *
  omega

theorem linPrimaryMatrixFullCost_poly : PBU (fun _ W _ => linPrimaryMatrixFullCost W) := by
  have hm : PBU (fun _ W _ => linPrimaryMatrixFullModBudget W) :=
    linPoly_subst linModMatrixCost_poly (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linPrimaryMatrixFullArg W) := PBU.smul 100 (PBU.addc (PBU.add PBU.W hm) 1)
  have hb : PBU (fun _ W _ => linPrimaryMatrixFullBuildBudget W) :=
    linPoly_subst linPrimaryMatrixCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hm) hb) 1)

end GI.Impl
