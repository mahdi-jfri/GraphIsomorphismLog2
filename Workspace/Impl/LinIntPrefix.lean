module

public import Workspace.Impl.LinOrders
public import Workspace.Impl.LinIntPad
public import Workspace.Lang.Prims.Blocks
public import Workspace.Impl.LinIntPoly

@[expose] public section

/-! Construct the prefix permutation-group values U_i = <N,a_1,...,a_i>. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- Input [generators of N,generators of A,i]. Drop the encoding's identity,
copy the first i A-generators, and append them to the N-generators. -/
def linPrefixF (tail take append : ℕ) : Expr :=
  .letE (.call tail (.get (arg 1) (.nat 1)))
    (.letE (.call take (mk2 (arg 2) (.var 1)))
      (mk2 (.get (arg 0) (.nat 0)) (.call append (mk2 (.get (arg 0) (.nat 1)) (.var 2)))))

def linPrefixCost (W : ℕ) : ℕ := 10 ^ 8 * (W + 1) ^ 4

set_option maxHeartbeats 1000000 in
theorem linPrefix_spec {P : Program} {f tail take append n : ℕ}
    (hf : P.funs[f]? = some (linPrefixF tail take append))
    (ht : P.HasAt tail (linTailFuns tail)) (hk : P.HasAt take (linTakeFuns take))
    (ha : P.HasAt append (appendFuns append))
    (ns as : List (Equiv.Perm (Fin n))) (i : ℕ) (hi : i ≤ as.length) :
    FunDet P f (.list [encGroup ns, encGroup as, .nat i]) (encGroup (ns ++ as.take i))
      (linPrefixCost (Val.list [encGroup ns, encGroup as, .nat i]).wt) := by
  let a := Val.list [encGroup ns, encGroup as, .nat i]
  let W := a.wt
  let xs := (1 :: ns).map encPerm
  let ys := as.map encPerm
  let out := xs ++ ys.take i
  have wgn : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have wn : (Val.list xs).wt < W :=
    (wt_le_wt_list (by simp [encGroup, encPerms, xs] : Val.list xs ∈ [.nat n, .list xs])).trans wgn
  have was : (encGroup as).wt < W := wt_le_wt_list (by simp)
  have wal : (Val.list ((1 :: as).map encPerm)).wt ≤ W :=
    (wt_le_wt_list (by simp : Val.list ((1 :: as).map encPerm) ∈ [.nat n, .list ((1 :: as).map encPerm)])).le.trans was.le
  have wy : (Val.list ys).wt ≤ W :=
    (wt_list_sublist (by simp [ys, encGroup, encPerms] : ys.Sublist ((1 :: as).map encPerm))).trans wal
  have wp : (Val.list (ys.take i)).wt ≤ W := (wt_list_sublist (List.take_sublist i ys)).trans wy
  have widx : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have hn := length_lt_wt_list xs
  have hy := length_lt_wt_list ys
  have hlen : out.length ≤ 2 * W := by
    simp only [out, List.length_append]
    have htake : (ys.take i).length ≤ ys.length := by simp only [List.length_take]; omega
    omega
  have wo : (Val.list out).wt ≤ 10 * (W + 1) ^ 2 := by
    have hh := linWtList (vs := out) (B := W) (by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (wt_le_wt_list hv).le.trans wn.le
      · exact (wt_le_wt_list (List.mem_of_mem_take hv)).le.trans wy)
    have hm := Nat.mul_le_mul_right W hlen
    ring_nf at *
    omega
  have ht0 := linTail_spec ht ((1 :: as).map encPerm)
  simp only [List.map_cons, List.drop_succ_cons, List.drop_zero] at ht0
  have ht1 := ht0.mono (show linTailCost (Val.list ((1 :: as).map encPerm)).wt ≤ linTailCost W by
    unfold linTailCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have wtka := wt_list2_le (.nat i) (.list ys)
  have wtka' : (Val.list [.nat i, .list ys]).wt ≤ 10 * (W + 1) := by omega
  have htk := (linTake_spec hk ys i (by simpa [ys] using hi)).mono (linTakeCost_mono wtka')
  have wappa := wt_list2_le (.list xs) (.list (ys.take i))
  have hlenp : (ys.take i).length ≤ W := by
    have htake : (ys.take i).length ≤ ys.length := by simp only [List.length_take]; omega
    omega
  have hap := linAppend_det ha xs (ys.take i)
  have darg (j : ℕ) (rest : List Val) {v : Val} (hv : [encGroup ns, encGroup as, .nat i][j]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup ns, encGroup as, .nat i]) (rest := rest) (j := j) hv
  have dt := Det.call (Det.get' (darg 1 [] rfl) (Det.nat 1) rfl) ht1
  have dk := Det.call (Det.mk2 (darg 2 [.list ys] rfl)
    (Det.var' (P := P) (env := [a, .list ys]) (i := 1) rfl)) htk
  have da := Det.call (Det.mk2 (Det.get' (darg 0 [.list ys, .list (ys.take i)] rfl) (Det.nat 1) rfl)
    (Det.var' (P := P) (env := [a, .list ys, .list (ys.take i)]) (i := 2) rfl)) hap
  have dd := Det.get' (darg 0 [.list ys, .list (ys.take i)] rfl) (Det.nat 0) rfl
  have db := Det.mk2 dd da
  have wgout := wt_list2_le (.nat n) (.list out)
  have wnd : (Val.nat n).wt < W := (wt_le_wt_list (by simp : Val.nat n ∈ [.nat n, .list xs])).trans wgn
  have heq : encGroup (ns ++ as.take i) = .list [.nat n, .list out] := by
    simp [encGroup, encPerms, out, xs, ys, List.map_take]
  rw [heq]
  apply FunDet.intro hf
  refine (Det.letE dt (Det.letE dk db)).mono ?_
  have haBound : loopModK * ((ys.take i).length + 1) *
      ((Val.list [.list xs, .list (ys.take i)]).wt + (ys.take i).length + (Val.list out).wt + 1) ≤
      1000 * (W + 1) * (10 * (W + 1) + W + 10 * (W + 1) ^ 2 + 1) := by
    simp only [loopModK]
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (by omega)
    · omega
  change _ ≤ linPrefixCost W
  unfold linPrefixCost
  have hTail : linTailCost W = 10000 * (W + 1) ^ 3 := rfl
  have hTake : linTakeCost (10 * (W + 1)) = 10000 * (10 * (W + 1) + 1) ^ 3 := rfl
  rw [hTail, hTake]
  simp only [W, a, xs, ys, out, encGroup, encPerms, List.map_cons] at *
  ring_nf at *
  omega

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrefix_gens {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : ℕ) :
    gens (ns ++ as.take i) = linChain (gens ns) as i := by
  simp only [gens, linChain]
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp

theorem linPrefixCost_mono {W V : ℕ} (h : W ≤ V) : linPrefixCost W ≤ linPrefixCost V := by
  unfold linPrefixCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)

/-- Input [N,A,i]. Construct the two prefixes and compute their order ratio. -/
def linPrefixOrderF (pf ratio : ℕ) : Expr :=
  .letE (.call pf (.var 0))
    (.letE (.call pf (mk3 (arg 0) (arg 1) (.arith .add (arg 2) (.nat 1))))
      (.call ratio (mk2 (.var 1) (.var 2))))

noncomputable def linPrefixOrderRatioCost (h : GroupOrder) (W n : ℕ) : ℕ :=
  2 * (groupOrderPrim h).boundSize (linPrefixCost (10 * (W + 1))) +
    4 * (4 * linPrefixCost (10 * (W + 1)) + 6) + 10 * (n ^ 2 + 4) + 20

noncomputable def linPrefixOrderCost (h : GroupOrder) (W n : ℕ) : ℕ :=
  1000 * (W + n + linPrefixCost (10 * (W + 1)) + linPrefixOrderRatioCost h W n + 1)

set_option maxHeartbeats 1000000 in
theorem linPrefixOrder_spec (h : GroupOrder) {P : Program} {f pf ratio j tail take append n : ℕ}
    (hf : P.funs[f]? = some (linPrefixOrderF pf ratio))
    (hp : P.funs[pf]? = some (linPrefixF tail take append))
    (ht : P.HasAt tail (linTailFuns tail)) (hk : P.HasAt take (linTakeFuns take))
    (ha : P.HasAt append (appendFuns append))
    (hr : P.funs[ratio]? = some (linOrderRatioF j))
    (hj : P.prims[j]? = some (groupOrderPrim h))
    (ns as : List (Equiv.Perm (Fin n))) (i : ℕ) (hi : i < as.length) :
    FunDet P f (.list [encGroup ns, encGroup as, .nat i])
      (.nat ((linChain (gens ns) as i).relIndex (linChain (gens ns) as (i + 1))))
      (linPrefixOrderCost h (Val.list [encGroup ns, encGroup as, .nat i]).wt n) := by
  let a := Val.list [encGroup ns, encGroup as, .nat i]
  let W := a.wt
  let V := linPrefixCost (10 * (W + 1))
  let g := encGroup (ns ++ as.take i)
  let k := encGroup (ns ++ as.take (i + 1))
  have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp)
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp)
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have hlen : as.length < W := by
    have wlist : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have hl := (length_lt_wt_list ((1 :: as).map encPerm)).trans wlist
    simp only [List.length_map, List.length_cons] at hl
    exact lt_of_lt_of_le (by omega : as.length < (encGroup as).wt) wa.le
  have wip := wt_nat_le (i + 1)
  have win := wt_list3_le (encGroup ns) (encGroup as) (.nat (i + 1))
  have win' : (Val.list [encGroup ns, encGroup as, .nat (i + 1)]).wt ≤ 10 * (W + 1) := by omega
  have hg := (linPrefix_spec hp ht hk ha ns as i hi.le).mono (linPrefixCost_mono (by omega : W ≤ 10 * (W + 1)))
  have hk' := (linPrefix_spec hp ht hk ha ns as (i + 1) (by omega)).mono (linPrefixCost_mono win')
  have wg : g.wt ≤ V := hg.wt_lt.le
  have wk : k.wt ≤ V := hk'.wt_lt.le
  have gh : GroupVal n g (linChain (gens ns) as i) := GensVal.groupVal (linPrefix_gens ns as i)
  have kh : GroupVal n k (linChain (gens ns) as (i + 1)) := GensVal.groupVal (linPrefix_gens ns as (i + 1))
  have hrat := linOrderRatio_spec h hr hj gh kh (linChain_mono _ _ (Nat.le_succ i))
  have hcost : linOrderRatioCost h n g k ≤ linPrefixOrderRatioCost h W n := by
    have hb1 := (groupOrderPrim h).bound_le (g.size_le_wt.trans wg)
    have hb2 := (groupOrderPrim h).bound_le (k.size_le_wt.trans wk)
    have wpair := wt_list2_le g k
    unfold linOrderRatioCost linPrefixOrderRatioCost
    change _ ≤ 2 * (groupOrderPrim h).boundSize V + 4 * (4 * V + 6) + 10 * (n ^ 2 + 4) + 20
    omega
  have hrat' := hrat.mono hcost
  have wo := hrat'.wt_lt.le
  have darg (idx : ℕ) (rest : List Val) {v : Val} (hv : [encGroup ns, encGroup as, .nat i][idx]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup ns, encGroup as, .nat i]) (rest := rest) (j := idx) hv
  have dg := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hg
  have dn := Det.arith (op := .add) (darg 2 [g] rfl) (Det.nat 1)
  simp only [GI.Machine.BinOp.eval_add] at dn
  have dk := Det.call (Det.mk3 (darg 0 [g] rfl) (darg 1 [g] rfl) dn) hk'
  have dr := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, g, k]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, g, k]) (i := 2) rfl)) hrat'
  apply FunDet.intro hf
  refine (Det.letE dg (Det.letE dk dr)).mono ?_
  have wpair := wt_list2_le g k
  change _ ≤ linPrefixOrderCost h W n
  unfold linPrefixOrderCost
  simp only [g, k, V, W, a] at *
  omega

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrefixOrderCost_poly (h : GroupOrder) : PBU (fun n W _ => linPrefixOrderCost h W n) := by
  simp only [linPrefixOrderCost, linPrefixOrderRatioCost, linPrefixCost, Prim.boundSize]
  norm_poly

end GI.Impl
