import Workspace.Impl.LinRecenterOffset

namespace GI.Impl
open GI.Cited GI.Lang

def linFiniteDifferenceF (sub rem : ℕ) : Expr :=
  .letE (.call sub (mk2 (arg 1) (arg 2))) (.call rem (mk2 (.var 1) (arg 0)))

def linFiniteDifferenceFuns (b : ℕ) : List Expr :=
  [linFiniteDifferenceF (b + 1) (b + 4)] ++
    linVectorBinaryFuns (b + 1) ((b + 7) + 12) ++ linFiniteReduceFuns (b + 4)

theorem linFiniteDifferenceFuns_length (b : ℕ) : (linFiniteDifferenceFuns b).length = 25 := rfl

structure linFiniteDifferenceAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linFiniteDifferenceF (b + 1) (b + 4))
  sub : P.HasAt (b + 1) (linVectorBinaryFuns (b + 1) ((b + 7) + 12))
  rem : P.HasAt (b + 4) (linFiniteReduceFuns (b + 4))

theorem linFiniteDifferenceAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linFiniteDifferenceFuns b)) : linFiniteDifferenceAt P b where
  entry := (h.block (gs := [linFiniteDifferenceF (b + 1) (b + 4)]) 0 rfl).single
  sub := h.block 1 rfl
  rem := h.block 4 rfl

def linFiniteDifferenceSubBudget (W : ℕ) : ℕ := linRecenterVectorCost (100 * (W + 1)) W
def linFiniteDifferenceRemArg (W : ℕ) : ℕ := 100 * (W + linFiniteDifferenceSubBudget W + 1)
def linFiniteDifferenceRemBudget (W : ℕ) : ℕ := linFiniteReduceCost (linFiniteDifferenceRemArg W) W
def linFiniteDifferenceCost (W : ℕ) : ℕ :=
  100000 * (W + linFiniteDifferenceSubBudget W + linFiniteDifferenceRemBudget W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem linFiniteDifference_spec {P : Program} {b d : ℕ} (h : linFiniteDifferenceAt P b)
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (v w : linFiniteVec m) :
    let a := Val.list [linVecVal (fun i => (m i : ℤ)),
      linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]
    FunDet P b a (linFiniteIntVecVal m (v - w)) (linFiniteDifferenceCost a.wt) := by
  let orders := linVecVal (fun i => (m i : ℤ))
  let vv := linVecVal (fun i => ((v i).val : ℤ))
  let wv := linVecVal (fun i => ((w i).val : ℤ))
  let a := Val.list [orders, vv, wv]
  let W := a.wt
  let diff := linVecVal (fun i => ((v i).val : ℤ) - ((w i).val : ℤ))
  let out := linFiniteIntVecVal m (v - w)
  have wo : orders.wt < W := wt_le_wt_list (by simp [a, W])
  have wv0 : vv.wt < W := wt_le_wt_list (by simp [a, W])
  have ww : wv.wt < W := wt_le_wt_list (by simp [a, W])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => encInt (m i : ℤ))
    simp only [List.length_map, List.length_finRange] at hh
    change d < orders.wt at hh
    omega
  have wsa : (Val.list [vv, wv]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le vv wv
    omega
  have hi := linInt_spec (h.rem.block 3 rfl)
  have hs := (linVectorSub_spec hi h.sub (fun i => ((v i).val : ℤ)) (fun i => ((w i).val : ℤ))).mono
    (linRecenterVectorCost_mono wsa hd)
  have wd : diff.wt ≤ linFiniteDifferenceSubBudget W := hs.wt_lt.le
  have wra : (Val.list [diff, orders]).wt ≤ linFiniteDifferenceRemArg W := by
    have hh := wt_list2_le diff orders
    unfold linFiniteDifferenceRemArg
    omega
  have hr := (linFiniteReduce_spec h.rem m hm (fun i => ((v i).val : ℤ) - ((w i).val : ℤ))).mono
    (linRecenterReduceCost_mono wra hd)
  have he : (fun i => ((((v i).val : ℤ) - ((w i).val : ℤ) : ℤ) : ZMod (m i))) = v - w := by
    funext i
    haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
    simp [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [he] at hr
  have wout : out.wt ≤ linFiniteDifferenceRemBudget W := hr.wt_lt.le
  have dv := Det.arg' (P := P) (vs := [orders, vv, wv]) (rest := []) (j := 1) rfl
  have dw := Det.arg' (P := P) (vs := [orders, vv, wv]) (rest := []) (j := 2) rfl
  have ds := Det.call (Det.mk2 dv dw) hs
  have dr := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, diff]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := [orders, vv, wv]) (rest := [diff]) (j := 0) rfl)) hr
  apply FunDet.intro h.entry
  refine (Det.letE ds dr).mono ?_
  have warg1 := wt_list2_le vv wv
  have warg2 := wt_list2_le diff orders
  change _ ≤ linFiniteDifferenceCost W
  unfold linFiniteDifferenceCost
  dsimp only [W, a, diff, out, orders, vv, wv,
    linFiniteDifferenceSubBudget, linFiniteDifferenceRemBudget] at *
  omega

theorem linFiniteDifferenceCost_mono {W V : ℕ} (h : W ≤ V) :
    linFiniteDifferenceCost W ≤ linFiniteDifferenceCost V := by
  have hs : linFiniteDifferenceSubBudget W ≤ linFiniteDifferenceSubBudget V :=
    linRecenterVectorCost_mono (by omega) h
  have hr : linFiniteDifferenceRemBudget W ≤ linFiniteDifferenceRemBudget V :=
    linRecenterReduceCost_mono (show linFiniteDifferenceRemArg W ≤ linFiniteDifferenceRemArg V by
      unfold linFiniteDifferenceRemArg; omega) h
  unfold linFiniteDifferenceCost
  omega

set_option maxRecDepth 12000 in
theorem linFiniteDifferenceCost_poly : PBU (fun _ W _ => linFiniteDifferenceCost W) := by
  have hs := linPoly_subst linRecenterVectorCost_poly PBU.W
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linFiniteDifferenceRemArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hs) 1)
  have hr := linPoly_subst linFiniteReduceCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hs) hr) 1)

end GI.Impl
