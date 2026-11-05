module

public import Workspace.Impl.LinPrimaryVector
public import Workspace.Impl.LinFiniteActionCost

@[expose] public section

/-! Extract the full stored translation column, then take its divided layer
coordinates. This retains the signed full action between successive layers. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryOffsetF (column vector : ℕ) : Expr :=
  .letE (.call column (mk2 (.length (arg 3)) (.get (arg 0) (.nat 1))))
    (.call vector (mk4 (arg 1) (arg 2) (.var 1) (arg 3)))
def linPrimaryOffsetFuns (b : ℕ) : List Expr :=
  [linPrimaryOffsetF (b + 1) (b + 5)] ++ linColumnFuns (b + 1) ++ linPrimaryVectorFuns (b + 5)

theorem linPrimaryOffsetFuns_length (b : ℕ) : (linPrimaryOffsetFuns b).length = 33 := rfl

structure linPrimaryOffsetAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryOffsetF (b + 1) (b + 5))
  column : P.HasAt (b + 1) (linColumnFuns (b + 1))
  vector : linPrimaryVectorAt P (b + 5)

theorem linPrimaryOffsetAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryOffsetFuns b)) : linPrimaryOffsetAt P b where
  entry := (h.block (gs := [linPrimaryOffsetF (b + 1) (b + 5)]) 0 rfl).single
  column := h.block 1 rfl
  vector := linPrimaryVectorAt_of (h.block 5 rfl)

def linPrimaryOffsetColumnBudget (W : ℕ) : ℕ := linColumnCost (100 * (W + 1)) (W + 1)
def linPrimaryOffsetArg (W : ℕ) : ℕ := 100 * (W + linPrimaryOffsetColumnBudget W + 1)
def linPrimaryOffsetVectorBudget (W : ℕ) : ℕ := linPrimaryVectorCost (linPrimaryOffsetArg W) W

def linPrimaryOffsetCost (W : ℕ) : ℕ :=
  100000 * (W + linPrimaryOffsetColumnBudget W + linPrimaryOffsetVectorBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 6000 in
theorem linPrimaryOffset_spec {P : Program} {b p d : ℕ} (h : linPrimaryOffsetAt P b)
    (hp : 0 < p) (ν : Fin d → ℕ) (level : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (u : linFiniteVec (linPrimaryOrders p ν)) (inv : Val) :
    let m := linPrimaryOrders p ν
    let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
    let a := Val.list [record, .nat p, .nat (p ^ level), encFun ν]
    FunDet P b a (encVec (linPrimaryCoord p ν level u)) (linPrimaryOffsetCost a.wt) := by
  let m := linPrimaryOrders p ν
  let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
  let a := Val.list [record, .nat p, .nat (p ^ level), encFun ν]
  let W := a.wt
  let x := linExtend (fun i => (u i).val) 1
  have wrec : record.wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W, a])
  have wq : (Val.nat (p ^ level)).wt < W := wt_le_wt_list (by simp [W, a])
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have wmat : (encIntMatrix (linFiniteHomogeneous m f u)).wt < record.wt := wt_le_wt_list (by simp [record])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have he : (fun i => linFiniteHomogeneous m f u i (Fin.last d)) = (fun i => (x i : ℤ)) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [linFiniteHomogeneous, linAffineMatrix, x]
    | cast i => simp [linFiniteHomogeneous, linAffineMatrix, x]
  have warg : (Val.list [.nat d, encIntMatrix (linFiniteHomogeneous m f u)]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat d) (encIntMatrix (linFiniteHomogeneous m f u))
    have hw := wt_nat_le d
    omega
  have hc := (linColumn_spec h.column (linFiniteHomogeneous m f u) (Fin.last d)).mono
    (linColumnCost_mono warg (d + 1))
  rw [he] at hc
  have hc' : FunDet P (b + 1) (.list [.nat d, encIntMatrix (linFiniteHomogeneous m f u)])
      (linVecVal (fun i => (x i : ℤ))) (linPrimaryOffsetColumnBudget W) := hc.mono (by
    unfold linPrimaryOffsetColumnBudget linColumnCost linVectorAccWt
    gcongr)
  have wx := hc'.wt_lt.le
  have wvarg : (Val.list [.nat p, .nat (p ^ level), linVecVal (fun i => (x i : ℤ)), encFun ν]).wt ≤
      linPrimaryOffsetArg W := by
    have hh := wt_list4_le (.nat p) (.nat (p ^ level)) (linVecVal (fun i => (x i : ℤ))) (encFun ν)
    unfold linPrimaryOffsetArg
    omega
  have hv := (linPrimaryVector_spec h.vector hp (p ^ level) x ν).mono
    (linPrimaryVectorCost_mono wvarg hd)
  have ho : (fun i : Fin d => ((x i.castSucc / p ^ level : ℕ) : ZMod p)) = linPrimaryCoord p ν level u := by
    funext i
    simp only [x, linExtend_castSucc, linPrimaryCoord]
  rw [ho] at hv
  change FunDet P (b + 5) (.list [.nat p, .nat (p ^ level), linVecVal (fun i => (x i : ℤ)), encFun ν])
    (encVec (linPrimaryCoord p ν level u)) (linPrimaryOffsetVectorBudget W) at hv
  have wo := hv.wt_lt.le
  have dr := Det.arg' (P := P) (vs := [record, .nat p, .nat (p ^ level), encFun ν]) (rest := []) (j := 0) rfl
  have dν := Det.arg' (P := P) (vs := [record, .nat p, .nat (p ^ level), encFun ν]) (rest := []) (j := 3) rfl
  have dn := Det.length dν
  simp only [List.length_map, List.length_finRange] at dn
  have dc := Det.call (Det.mk2 dn (Det.get' dr (Det.nat 1) rfl)) hc'
  have dp := Det.arg' (P := P) (vs := [record, .nat p, .nat (p ^ level), encFun ν])
    (rest := [linVecVal (fun i => (x i : ℤ))]) (j := 1) rfl
  have dq := Det.arg' (P := P) (vs := [record, .nat p, .nat (p ^ level), encFun ν])
    (rest := [linVecVal (fun i => (x i : ℤ))]) (j := 2) rfl
  have dν' := Det.arg' (P := P) (vs := [record, .nat p, .nat (p ^ level), encFun ν])
    (rest := [linVecVal (fun i => (x i : ℤ))]) (j := 3) rfl
  have dv := Det.call (Det.mk4 dp dq
    (Det.var' (P := P) (env := [a, linVecVal (fun i => (x i : ℤ))]) (i := 1) rfl) dν') hv
  apply FunDet.intro h.entry
  refine (Det.letE dc dv).mono ?_
  have wi := wt_list2_le (.nat d) (encIntMatrix (linFiniteHomogeneous m f u))
  have wb := wt_list4_le (.nat p) (.nat (p ^ level)) (linVecVal (fun i => (x i : ℤ))) (encFun ν)
  change _ ≤ linPrimaryOffsetCost W
  unfold linPrimaryOffsetCost
  dsimp only [a, W, record, encFun] at *
  omega

theorem linPrimaryOffsetCost_poly : PBU (fun _ W _ => linPrimaryOffsetCost W) := by
  have hc : PBU (fun _ W _ => linPrimaryOffsetColumnBudget W) := by
    unfold linPrimaryOffsetColumnBudget linColumnCost linVectorAccWt
    norm_poly
  have ha : PBU (fun _ W _ => linPrimaryOffsetArg W) := PBU.smul 100 (PBU.addc (PBU.add PBU.W hc) 1)
  have hv : PBU (fun _ W _ => linPrimaryOffsetVectorBudget W) :=
    linPoly_subst linPrimaryVectorCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hc) hv) 1)

end GI.Impl
