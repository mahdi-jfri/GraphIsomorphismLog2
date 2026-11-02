import Workspace.Impl.LinFiniteRecenterMatrix
import Workspace.Impl.LinMatrixVec
import Workspace.Impl.LinFiniteReduce

/-! Compute Rw + c - w in full finite-abelian coordinates. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linRecenterOffsetF (mul add sub rem : ℕ) : Expr :=
  .letE (.call mul (mk2 (arg 3) (arg 1)))
    (.letE (.call add (mk2 (.var 1) (arg 2)))
      (.letE (.call sub (mk2 (.var 2) (arg 3))) (.call rem (mk2 (.var 3) (arg 0)))))

def linRecenterOffsetFuns (b : ℕ) : List Expr :=
  [linRecenterOffsetF (b + 1) (b + 26) (b + 29) (b + 32)] ++ linMatrixVecFuns (b + 1) ++
    linVectorBinaryFuns (b + 26) ((b + 8) + 11) ++
    linVectorBinaryFuns (b + 29) ((b + 8) + 12) ++ linFiniteReduceFuns (b + 32)

theorem linRecenterOffsetFuns_length (b : ℕ) : (linRecenterOffsetFuns b).length = 53 := rfl

structure linRecenterOffsetAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linRecenterOffsetF (b + 1) (b + 26) (b + 29) (b + 32))
  mul : linMatrixVecAt P (b + 1)
  add : P.HasAt (b + 26) (linVectorBinaryFuns (b + 26) ((b + 8) + 11))
  sub : P.HasAt (b + 29) (linVectorBinaryFuns (b + 29) ((b + 8) + 12))
  rem : P.HasAt (b + 32) (linFiniteReduceFuns (b + 32))

theorem linRecenterOffsetAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linRecenterOffsetFuns b)) : linRecenterOffsetAt P b where
  entry := (h.block (gs := [linRecenterOffsetF (b + 1) (b + 26) (b + 29) (b + 32)]) 0 rfl).single
  mul := linMatrixVecAt_of (h.block 1 rfl)
  add := h.block 26 rfl
  sub := h.block 29 rfl
  rem := h.block 32 rfl

def linRecenterVectorCost (W d : ℕ) : ℕ := linVectorBinaryCost W d (20 * (W + 2))
def linRecenterOffsetMulBudget (W : ℕ) : ℕ := linMatrixVecCost (100 * (W + 1)) W
def linRecenterOffsetAddArg (W : ℕ) : ℕ := 100 * (W + linRecenterOffsetMulBudget W + 1)
def linRecenterOffsetAddBudget (W : ℕ) : ℕ := linRecenterVectorCost (linRecenterOffsetAddArg W) W
def linRecenterOffsetSubArg (W : ℕ) : ℕ := 100 * (W + linRecenterOffsetAddBudget W + 1)
def linRecenterOffsetSubBudget (W : ℕ) : ℕ := linRecenterVectorCost (linRecenterOffsetSubArg W) W
def linRecenterOffsetRemArg (W : ℕ) : ℕ := 100 * (W + linRecenterOffsetSubBudget W + 1)
def linRecenterOffsetRemBudget (W : ℕ) : ℕ := linFiniteReduceCost (linRecenterOffsetRemArg W) W
def linRecenterOffsetCost (W : ℕ) : ℕ := 100000 * (W + linRecenterOffsetMulBudget W +
  linRecenterOffsetAddBudget W + linRecenterOffsetSubBudget W + linRecenterOffsetRemBudget W + 1)

theorem linRecenterVectorCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linRecenterVectorCost W d ≤ linRecenterVectorCost V e :=
  linVectorBinaryCost_mono hW hd (by omega)

theorem linRecenterReduceCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linFiniteReduceCost W d ≤ linFiniteReduceCost V e := by
  unfold linFiniteReduceCost
  exact linVectorBinaryCost_mono hW hd (by omega)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linRecenterOffset_spec {P : Program} {b d : ℕ} (h : linRecenterOffsetAt P b)
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (A : Matrix (Fin d) (Fin d) ℤ)
    (u w : Fin d → ℤ) :
    let a := Val.list [linVecVal (fun i => (m i : ℤ)), encIntMatrix A, linVecVal u, linVecVal w]
    FunDet P b a (linFiniteIntVecVal m (fun i => ((A.mulVec w i + u i - w i : ℤ) : ZMod (m i))))
      (linRecenterOffsetCost a.wt) := by
  let orders := linVecVal (fun i => (m i : ℤ))
  let a := Val.list [orders, encIntMatrix A, linVecVal u, linVecVal w]
  let W := a.wt
  let R := linVecVal (A.mulVec w)
  let S := linVecVal (fun i => A.mulVec w i + u i)
  let T := linVecVal (fun i => A.mulVec w i + u i - w i)
  let U := linFiniteIntVecVal m (fun i => ((A.mulVec w i + u i - w i : ℤ) : ZMod (m i)))
  have wo : orders.wt < W := wt_le_wt_list (by simp [a, W])
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [a, W])
  have wu : (linVecVal u).wt < W := wt_le_wt_list (by simp [a, W])
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp [a, W])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < orders.wt at hh
    omega
  have wma : (Val.list [linVecVal w, encIntMatrix A]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (linVecVal w) (encIntMatrix A)
    omega
  have hmul := (linMatrixVec_spec h.mul A w).mono (linMatrixVecCost_mono wma hd)
  have wR : R.wt ≤ linRecenterOffsetMulBudget W := hmul.wt_lt.le
  have waa : (Val.list [R, linVecVal u]).wt ≤ linRecenterOffsetAddArg W := by
    have hh := wt_list2_le R (linVecVal u)
    unfold linRecenterOffsetAddArg
    omega
  have hadd := (linVectorAdd_spec h.mul.ints h.add (A.mulVec w) u).mono (linRecenterVectorCost_mono waa hd)
  have wS : S.wt ≤ linRecenterOffsetAddBudget W := hadd.wt_lt.le
  have wsa : (Val.list [S, linVecVal w]).wt ≤ linRecenterOffsetSubArg W := by
    have hh := wt_list2_le S (linVecVal w)
    unfold linRecenterOffsetSubArg
    omega
  have hsub := (linVectorSub_spec h.mul.ints h.sub (fun i => A.mulVec w i + u i) w).mono
    (linRecenterVectorCost_mono wsa hd)
  have wT : T.wt ≤ linRecenterOffsetSubBudget W := hsub.wt_lt.le
  have wra : (Val.list [T, orders]).wt ≤ linRecenterOffsetRemArg W := by
    have hh := wt_list2_le T orders
    unfold linRecenterOffsetRemArg
    omega
  have hrem := (linFiniteReduce_spec h.rem m hm (fun i => A.mulVec w i + u i - w i)).mono
    (linRecenterReduceCost_mono wra hd)
  have wU : U.wt ≤ linRecenterOffsetRemBudget W := hrem.wt_lt.le
  have darg (rest : List Val) (j : ℕ) {v : Val}
      (hj : ([orders, encIntMatrix A, linVecVal u, linVecVal w] : List Val)[j]? = some v) :=
    Det.arg' (P := P) (vs := [orders, encIntMatrix A, linVecVal u, linVecVal w]) (rest := rest) (j := j) hj
  have dm := Det.call (Det.mk2 (darg [] 3 rfl) (darg [] 1 rfl)) hmul
  have da := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, R]) (i := 1) rfl) (darg [R] 2 rfl)) hadd
  have ds := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, R, S]) (i := 2) rfl) (darg [R, S] 3 rfl)) hsub
  have dr := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, R, S, T]) (i := 3) rfl) (darg [R, S, T] 0 rfl)) hrem
  apply FunDet.intro h.entry
  refine (Det.letE dm (Det.letE da (Det.letE ds dr))).mono ?_
  have wmarg := wt_list2_le (linVecVal w) (encIntMatrix A)
  have waarg := wt_list2_le R (linVecVal u)
  have wsarg := wt_list2_le S (linVecVal w)
  have wrarg := wt_list2_le T orders
  change _ ≤ linRecenterOffsetCost W
  unfold linRecenterOffsetCost
  dsimp only [W, a, orders, R, S, T, U, linRecenterOffsetMulBudget,
    linRecenterOffsetAddBudget, linRecenterOffsetSubBudget, linRecenterOffsetRemBudget] at *
  omega

theorem linRecenterOffset_action_spec {P : Program} {b d : ℕ} {G : Type*} [Group G]
    (h : linRecenterOffsetAt P b) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (w : linFiniteVec m) (g : G) :
    let a := Val.list [linVecVal (fun i => (m i : ℤ)),
      encIntMatrix (linFiniteIntMatrix m (ρ g).toAddMonoidHom),
      linVecVal (fun i => ((c g i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]
    FunDet P b a (linVecVal (fun i => ((linFiniteRecenter ρ c w g i).val : ℤ)))
      (linRecenterOffsetCost a.wt) := by
  have hs := linRecenterOffset_spec h m hm (linFiniteIntMatrix m (ρ g).toAddMonoidHom)
    (fun i => ((c g i).val : ℤ)) (fun i => ((w i).val : ℤ))
  unfold linFiniteIntVecVal at hs
  rw [linFiniteRecenter_cast m hm ρ c w g] at hs
  exact hs

theorem linRecenterOffsetCost_mono {W V : ℕ} (h : W ≤ V) :
    linRecenterOffsetCost W ≤ linRecenterOffsetCost V := by
  have hm : linRecenterOffsetMulBudget W ≤ linRecenterOffsetMulBudget V :=
    linMatrixVecCost_mono (by omega) h
  have ha : linRecenterOffsetAddBudget W ≤ linRecenterOffsetAddBudget V :=
    linRecenterVectorCost_mono (show linRecenterOffsetAddArg W ≤ linRecenterOffsetAddArg V by
      unfold linRecenterOffsetAddArg; omega) h
  have hs : linRecenterOffsetSubBudget W ≤ linRecenterOffsetSubBudget V :=
    linRecenterVectorCost_mono (show linRecenterOffsetSubArg W ≤ linRecenterOffsetSubArg V by
      unfold linRecenterOffsetSubArg; omega) h
  have hr : linRecenterOffsetRemBudget W ≤ linRecenterOffsetRemBudget V :=
    linRecenterReduceCost_mono (show linRecenterOffsetRemArg W ≤ linRecenterOffsetRemArg V by
      unfold linRecenterOffsetRemArg; omega) h
  unfold linRecenterOffsetCost
  omega

theorem linRecenterVectorCost_poly : PBU (fun d W _ => linRecenterVectorCost W d) := by
  unfold linRecenterVectorCost linVectorBinaryCost linVectorAccWt
    linIntBinaryCost linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem linRecenterOffsetCost_poly : PBU (fun _ W _ => linRecenterOffsetCost W) := by
  have hm := linPoly_subst linMatrixVecCost_poly PBU.W
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have haa : PBU (fun _ W _ => linRecenterOffsetAddArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hm) 1)
  have ha := linPoly_subst linRecenterVectorCost_poly PBU.W haa (PBU.const 0)
  have hsa : PBU (fun _ W _ => linRecenterOffsetSubArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W ha) 1)
  have hs := linPoly_subst linRecenterVectorCost_poly PBU.W hsa (PBU.const 0)
  have hra : PBU (fun _ W _ => linRecenterOffsetRemArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hs) 1)
  have hr := linPoly_subst linFiniteReduceCost_poly PBU.W hra (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hm) ha) hs) hr) 1)

end GI.Impl
