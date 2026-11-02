import Workspace.Impl.LinMapEncoded
import Workspace.Lang.Prims.Graph

/-! Build the disjoint union of two permutation tables. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

theorem linSumPerm_value {n : ℕ} (a b : Perm (Fin n)) :
    encPerm (sumToFin (Equiv.sumCongr a b)) =
      .list (((List.finRange n).map fun i => .nat (a i)) ++
        ((List.finRange n).map fun i => .nat (n + (b i : ℕ)))) := by
  apply congrArg Val.list
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_map, List.getElem_finRange]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_map, List.getElem_finRange, sumToFin_sumCongr_apply, Fin.coe_cast, Fin.val_mk, h, dif_pos]
    rfl
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange,
      sumToFin_sumCongr_apply, Fin.coe_cast, Fin.val_mk, h, dif_neg]
    rfl

def linSumPermPointF : Expr := .arith .add (arg 0) (arg 1)
def linSumPermF (map append : ℕ) : Expr :=
  .letE (.length (arg 0))
    (.letE (.call map (mk2 (.var 1) (arg 1)))
      (.call append (mk2 (arg 0) (.var 2))))
def linSumPermFuns (b : ℕ) : List Expr :=
  [linSumPermF (b + 2) (b + 5), linSumPermPointF] ++
    mapFuns (b + 2) (b + 1) ++ appendFuns (b + 5)

theorem linSumPermFuns_length (b : ℕ) : (linSumPermFuns b).length = 8 := rfl

theorem linSumPermPoint_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some linSumPermPointF)
    (n x W : ℕ) (hn : n ≤ W) (hx : x ≤ W) :
    FunDet P f (.list [.nat n, .nat x]) (.nat (n + x)) (100 * (W + 1)) := by
  have dn := Det.arg' (P := P) (vs := [.nat n, .nat x]) (rest := []) (j := 0) rfl
  have dx := Det.arg' (P := P) (vs := [.nat n, .nat x]) (rest := []) (j := 1) rfl
  apply FunDet.intro hf
  refine (Det.arith (op := .add) dn dx).mono ?_
  have wn := wt_nat_le n
  have wx := wt_nat_le x
  have ws := wt_nat_le (n + x)
  have wi := wt_list2_le (.nat n) (.nat x)
  simp only [GI.Machine.BinOp.eval_add]
  omega

theorem linMapBudget_mono {W V B C : ℕ} (hW : W ≤ V) (hB : B ≤ C) :
    linMapBudget W B ≤ linMapBudget V C := by
  unfold linMapBudget
  gcongr

def linSumPermMapBudget (W : ℕ) : ℕ := linMapBudget (10 * (W + 1)) (100 * (W + 1))
def linSumPermAppendBudget (W : ℕ) : ℕ :=
  loopModK * (W + 1) * (2 * (W + 10 * (W + 1) ^ 2) + 6 + W + 16 * (W + 1) ^ 2 + 1)
def linSumPermCost (W : ℕ) : ℕ :=
  10000 * (W + linSumPermMapBudget W + linSumPermAppendBudget W + 16 * (W + 1) ^ 2 + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linSumPerm_spec {P : Program} {b n : ℕ} (hp : P.HasAt b (linSumPermFuns b))
    (a c : Perm (Fin n)) :
    FunDet P b (.list [encPerm a, encPerm c]) (encPerm (sumToFin (Equiv.sumCongr a c)))
      (linSumPermCost (Val.list [encPerm a, encPerm c]).wt) := by
  let arg := Val.list [encPerm a, encPerm c]
  let W := arg.wt
  let ys := (List.finRange n).map fun i => Val.nat (n + (c i : ℕ))
  let xs := (List.finRange n).map fun i => Val.nat (a i)
  have wa : (encPerm a).wt < W := wt_le_wt_list (by simp [W, arg])
  have wc : (encPerm c).wt < W := wt_le_wt_list (by simp [W, arg])
  have hn : n ≤ W := by
    have hh := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (a i))
    simp only [List.length_map, List.length_finRange] at hh
    exact hh.le.trans wa.le
  have wn := wt_nat_le n
  have wmap := wt_list2_le (.nat n) (encPerm c)
  have wm : (Val.list [.nat n, encPerm c]).wt ≤ 10 * (W + 1) := by omega
  have hpoint := (hp.block (gs := [linSumPermPointF]) 1 rfl).single
  have hm := linMapEncoded_spec (hp.block 2 rfl) (fun i : Fin n => Val.nat (c i))
    (fun i j h => c.injective (Fin.ext (Val.nat.inj h)))
    (fun i => Val.nat (n + (c i : ℕ))) (.nat n) (List.finRange n) (100 * (W + 1))
    (fun i _ => linSumPermPoint_spec hpoint n (c i) W hn ((c i).isLt.le.trans hn))
  have hm' := hm.mono (linMapBudget_mono wm le_rfl)
  have wy : (Val.list ys).wt ≤ 10 * (W + 1) ^ 2 := by
    have hh := wt_encFun_le (fun i : Fin n => n + (c i : ℕ))
      (B := 2 * n) (fun i => by have := (c i).isLt; dsimp only; omega)
    change (Val.list ys).wt ≤ _ at hh
    have hpow : (n + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have wo := wt_encPerm_sum_le (sumToFin (Equiv.sumCongr a c))
  have wow : (encPerm (sumToFin (Equiv.sumCongr a c))).wt ≤ 16 * (W + 1) ^ 2 :=
    wo.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have we : encPerm (sumToFin (Equiv.sumCongr a c)) = .list (xs ++ ys) := linSumPerm_value a c
  have wi := wt_list2_le (encPerm a) (.list ys)
  have hap := append_spec (hp.block 5 rfl) xs ys
  have hap' : FunDet P (b + 5) (.list [encPerm a, .list ys])
      (encPerm (sumToFin (Equiv.sumCongr a c))) (linSumPermAppendBudget W) := by
    refine hap.mono fun w cost hw => ⟨hw.1.trans we.symm, ?_⟩
    have hc := hw.2
    rw [hw.1] at hc
    rw [← we] at hc
    have hys : ys.length = n := by simp [ys]
    rw [hys] at hc
    have hwArg : (Val.list [Val.list xs, Val.list ys]).wt + n +
        (encPerm (sumToFin (Equiv.sumCongr a c))).wt + 1 ≤
        2 * (W + 10 * (W + 1) ^ 2) + 6 + W + 16 * (W + 1) ^ 2 + 1 := by
      have wxs : (Val.list [Val.list xs, Val.list ys]).wt ≤
          2 * ((encPerm a).wt + (Val.list ys).wt) + 6 := wi
      omega
    exact hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hwArg)
  have dn := Det.length (Det.arg' (P := P) (vs := [encPerm a, encPerm c]) (rest := []) (j := 0) rfl)
  simp only [List.length_map, List.length_finRange] at dn
  have dmap := Det.call (Det.mk2
    (Det.var' (P := P) (env := [arg, .nat n]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := [encPerm a, encPerm c]) (rest := [.nat n]) (j := 1) rfl)) hm'
  have dapp := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encPerm a, encPerm c]) (rest := [.nat n, .list ys]) (j := 0) rfl)
    (Det.var' (P := P) (env := [arg, .nat n, .list ys]) (i := 2) rfl)) hap'
  apply FunAll.intro (hp.block (gs := [linSumPermF (b + 2) (b + 5)]) 0 rfl).single
  refine (Det.letE dn (Det.letE dmap dapp)).post fun cost hc => ⟨rfl, ?_⟩
  change cost ≤ linSumPermCost W
  unfold linSumPermCost
  have wpow : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have w₁ := wt_list2_le (encPerm a) (.list ys)
  dsimp only [arg, W, xs, ys, linSumPermMapBudget] at *
  omega

theorem linSumPermCost_poly : PBU (fun _ W _ => linSumPermCost W) := by
  unfold linSumPermCost linSumPermMapBudget linSumPermAppendBudget linMapBudget
  norm_poly

end GI.Impl
