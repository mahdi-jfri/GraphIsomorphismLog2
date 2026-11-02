import Workspace.Impl.LinAffineCallerAt
import Workspace.Impl.LinAffineCallerMath

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

def linAffineCallerOneAnswerE : Expr :=
  mk2 linAffineCallerIdentityE (mk2 (.get (arg 0) (.nat 0)) (mk1 linAffineCallerIdentityE))

set_option maxHeartbeats 1000000 in
theorem linAffineCallerOneAnswer_det {P : Program} {n : ℕ}
    (gs : List (Equiv.Perm (Fin n))) (orders raw v w : Val) (rest : List Val) :
    let a := Val.list [encGroup gs, orders, raw, v, w]
    Det P ([a] ++ rest) linAffineCallerOneAnswerE
      (.list [encPerm (1 : Equiv.Perm (Fin n)), encGroup ([] : List (Equiv.Perm (Fin n)))])
      (100000 * (a.wt + 1)) := by
  let a := Val.list [encGroup gs, orders, raw, v, w]
  have dg := Det.arg' (P := P) (vs := [encGroup gs, orders, raw, v, w]) (rest := rest) (j := 0) rfl
  have dl := Det.get' dg (Det.nat 1) rfl
  have di := Det.get' dl (Det.nat 0) rfl
  have dn := Det.get' dg (Det.nat 0) rfl
  have dd := Det.mk2 di (Det.mk2 dn (Det.mk1 di))
  have wg : (encGroup gs).wt < a.wt := wt_le_wt_list (by simp [a])
  have wl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have wi : (encPerm (1 : Equiv.Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have wn : (Val.nat n).wt < (encGroup gs).wt := wt_le_wt_list (by simp [encGroup])
  have we1 := wt_list1_le (encPerm (1 : Equiv.Perm (Fin n)))
  have we2 := wt_list2_le (.nat n) (.list [encPerm (1 : Equiv.Perm (Fin n))])
  have we3 := wt_list2_le (encPerm (1 : Equiv.Perm (Fin n))) (encGroup ([] : List (Equiv.Perm (Fin n))))
  refine dd.mono ?_
  dsimp only [a, encGroup, encPerms] at *
  simp only [List.map_cons, List.map_nil] at *
  omega

def linAffineCallerDiffBudget (W : ℕ) : ℕ := linFiniteDifferenceCost (100 * (W + 1))
def linAffineCallerZeroBudget (W : ℕ) : ℕ := linZeroIntVectorCost (linAffineCallerDiffBudget W)
def linAffineCallerSmallCost (W : ℕ) : ℕ :=
  1000000 * (W + linAffineCallerDiffBudget W + linAffineCallerZeroBudget W + 1)

set_option maxHeartbeats 300000 in
theorem linAffineCallerSmall_spec (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jmem jm jv n d : ℕ} (hat : linAffineTransportAllAt P b jmem jm jv hmem hm hv)
    (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) :
    let a := tmGLAffIn gs m ρ c v w
    FunDet P (b + 2) a (if v = w then .list [encPerm (1 : Equiv.Perm (Fin n)),
      encGroup ([] : List (Equiv.Perm (Fin n)))] else .list []) (linAffineCallerSmallCost a.wt) := by
  rw [linTmGLAffIn_eq]
  let orders := linVecVal (fun i => (m i : ℤ))
  let raw := Val.list ((linActionGens gs).map (linPlainAffineVal m ρ c))
  let vv := linVecVal (fun i => ((v i).val : ℤ))
  let wv := linVecVal (fun i => ((w i).val : ℤ))
  let a := Val.list [encGroup gs, orders, raw, vv, wv]
  let W := a.wt
  let diff := linFiniteIntVecVal m (v - w)
  let z := decide (v = w)
  have wo : orders.wt < W := wt_le_wt_list (by simp [a, W])
  have wv0 : vv.wt < W := wt_le_wt_list (by simp [a, W])
  have ww : wv.wt < W := wt_le_wt_list (by simp [a, W])
  have warg : (Val.list [orders, vv, wv]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list3_le orders vv wv
    omega
  have hd := (linFiniteDifference_spec hat.difference m hmpos v w).mono (linFiniteDifferenceCost_mono warg)
  have wd : diff.wt ≤ linAffineCallerDiffBudget W := hd.wt_lt.le
  have hz := linZeroIntVector_spec hat.zero (fun i => (((v - w) i).val : ℤ))
  have he : (fun i => (((v - w) i).val : ℤ)) = 0 ↔ v = w :=
    (linFiniteIntVec_zero_iff m hmpos (v - w)).trans sub_eq_zero
  simp only [he] at hz
  have hz' := hz.mono (show linZeroIntVectorCost diff.wt ≤ linAffineCallerZeroBudget W by
    change 10000000 * (diff.wt + 1) ^ 3 ≤
      10000000 * (linAffineCallerDiffBudget W + 1) ^ 3
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right wd 1) 3))
  have darg (rest : List Val) (j : ℕ) {value : Val}
      (hj : ([encGroup gs, orders, raw, vv, wv] : List Val)[j]? = some value) :=
    Det.arg' (P := P) (vs := [encGroup gs, orders, raw, vv, wv]) (rest := rest) (j := j) hj
  have dd := Det.call (Det.mk3 (darg [] 1 rfl) (darg [] 3 rfl) (darg [] 4 rfl)) hd
  have dz := Det.call (Det.var' (P := P) (env := [a, diff]) (i := 1) rfl) hz'
  have db := Det.var' (P := P) (env := [a, diff, boolVal z]) (i := 2) rfl
  have wbool := wt_boolVal_le z
  have dans := linAffineCallerOneAnswer_det (P := P) gs orders raw vv wv [diff, boolVal z]
  have wans := linDet_wt_le dans
  apply FunDet.intro hat.small
  by_cases hEq : v = w
  · have hzval : boolVal z = .nat 1 := by simp [z, hEq, boolVal]
    rw [hzval] at db dans dz
    have de := Det.ite_pos (e := .nil) db (by decide : 1 ≠ 0) dans
    simp only [if_pos hEq]
    refine (Det.letE dd (Det.letE dz de)).mono ?_
    have hzwt := hz'.wt_lt.le
    change _ ≤ linAffineCallerSmallCost W
    unfold linAffineCallerSmallCost
    dsimp only [a, W, orders, raw, vv, wv, diff, z, linAffineCallerDiffBudget, linAffineCallerZeroBudget] at *
    simp only [hEq, decide_true, boolVal, Bool.toNat_true] at *
    omega
  · have hzval : boolVal z = .nat 0 := by simp [z, hEq, boolVal]
    rw [hzval] at db dz
    have de := Det.ite_zero (t := linAffineCallerOneAnswerE) db (Det.nil (P := P) (env := [a, diff, .nat 0]))
    simp only [if_neg hEq]
    refine (Det.letE dd (Det.letE dz de)).mono ?_
    have hzwt := hz'.wt_lt.le
    have wnil : (Val.list []).wt = 4 := rfl
    change _ ≤ linAffineCallerSmallCost W
    unfold linAffineCallerSmallCost
    dsimp only [a, W, orders, raw, vv, wv, diff, z, linAffineCallerDiffBudget, linAffineCallerZeroBudget] at *
    simp only [hEq, decide_false, boolVal, Bool.toNat_false] at *
    omega

end GI.Impl
