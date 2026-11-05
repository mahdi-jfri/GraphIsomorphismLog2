module

public import Workspace.Lang.Lib.LinIntMatrix
public import Workspace.Lang.Lib.SmallGroup

@[expose] public section

namespace GI.Lang
open GI.Cited (Val encInt encIntMatrix)

/-- Copy all entries after the first one. -/
def linTailStep : Expr :=
  .snoc (arg 2) (.get (arg 0) (.arith .add (arg 1) (.nat 1)))

def linTailFuns (b : ℕ) : List Expr :=
  loopFuns b (.arith .sub (.length (.var 0)) (.nat 1)) .nil linTailStep

def linTailCost (W : ℕ) : ℕ := 10000 * (W + 1) ^ 3

/-- List tail in polynomial bit cost, including copying arbitrary value entries. -/
theorem linTail_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linTailFuns b)) (xs : List Val) :
    FunDet P b (.list xs) (.list (xs.drop 1)) (linTailCost (Val.list xs).wt) := by
  let W := (Val.list xs).wt
  let k := xs.length - 1
  have hlen := length_lt_wt_list xs
  have hk := Det.arith (op := .sub) (Det.length (Det.var' (P := P) (env := [.list xs]) (i := 0) rfl))
    (Det.nat 1)
  have hwk : (Val.nat (xs.length - 1)).wt ≤ xs.length + 2 := by
    have := wt_nat_le (xs.length - 1); omega
  simp only [GI.Machine.BinOp.eval_sub] at hk
  have hacc (i : ℕ) : (Val.list ((xs.drop 1).take i)).wt ≤ W :=
    wt_list_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  have hlp : P.HasAt b (loopFuns b (.arith .sub (.length (.var 0)) (.nat 1)) .nil linTailStep) := hp
  have hloop := loopBdd_spec hlp hk Det.nil (by
    change (W + 1 + xs.length + 3 + (1 + 3) + (Val.nat (xs.length - 1)).wt + 1) + 5 ≤
      10 * (W + k + 1)
    have hW := (Val.list xs).two_le_size.trans (Val.list xs).size_le_wt
    change xs.length < W at hlen
    omega)
    (Inv := fun i acc => acc = .list ((xs.drop 1).take i)) (M := W) (D := fun _ => 1000 * (W + 1))
    (by simp) (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · have he := hw.1
      have hklen : k = (xs.drop 1).length := by simp [k]
      change w = .list ((xs.drop 1).take k) at he
      rw [hklen, List.take_length] at he
      exact he
    · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hw
      unfold linTailCost
      change cost ≤ 10000 * (W + 1) ^ 3
      have hcost := hw.2
      change cost ≤ k * (1000 * (W + 1)) + loopModK * (k + 1) * (W + k + W + 1) at hcost
      have hkw : k ≤ W := by unfold k W; omega
      simp only [loopModK] at hcost
      nlinarith [Nat.pow_le_pow_right (show 0 < W + 1 by omega) (show 2 ≤ 3 by decide)]
  · subst acc
    have hi' : i + 1 < xs.length := by omega
    have hx := List.getElem?_eq_getElem hi'
    have di := Det.arith (op := .add)
      (Det.arg' (P := P) (vs := [.list xs, .nat i, .list ((xs.drop 1).take i)]) (rest := []) (j := 1) rfl)
      (Det.nat 1)
    have dx := Det.get' (Det.arg' (P := P) (vs := [.list xs, .nat i, .list ((xs.drop 1).take i)])
      (rest := []) (j := 0) rfl) di hx
    have da := Det.arg' (P := P) (vs := [.list xs, .nat i, .list ((xs.drop 1).take i)]) (rest := []) (j := 2) rfl
    have dres := Det.snoc da dx
    have heq : (xs.drop 1).take (i + 1) = (xs.drop 1).take i ++ [xs[i + 1]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
      simp [List.getElem_drop, Nat.add_comm]
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list ((xs.drop 1).take i ++ [xs[i + 1]]) = Val.list ((xs.drop 1).take (i + 1))
      rw [heq]
    · have wx := wt_getElem_lt xs (i + 1) hi'
      have wa := hacc i
      have wo := hacc (i + 1)
      rw [heq] at wo
      have wi := wt_nat_le i
      have wi1 := wt_nat_le (i + 1)
      have ws := wt_list3_le (.list xs) (.nat i) (.list ((xs.drop 1).take i))
      beta_reduce at hc ⊢
      simp only [GI.Machine.BinOp.eval_add] at hc
      change cost ≤ 1000 * (W + 1) + 100 * (W + k + W + 1)
      have hkw : k ≤ W := by unfold k W; omega
      change (Val.list [.list xs, .nat i, .list ((xs.drop 1).take i)]).wt ≤
        2 * (W + (Val.nat i).wt + (Val.list ((xs.drop 1).take i)).wt) + 7 at ws
      change xs[i + 1].wt < W at wx
      omega

/-- The successor vector encoding splits at its first entry. -/
theorem linVecVal_succ {n : ℕ} (x : Fin (n + 1) → ℤ) :
    linVecVal x = .list (encInt (x 0) :: ((List.finRange n).map fun i => encInt (x i.succ))) := by
  simp [linVecVal, List.finRange_succ, List.map_map]

/-- Append with a fixed output-cost bound, for deterministic composition. -/
theorem linAppend_det {P : Program} {b : ℕ} (h : P.HasAt b (appendFuns b)) (xs ys : List Val) :
    FunDet P b (.list [.list xs, .list ys]) (.list (xs ++ ys))
      (loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length + (Val.list (xs ++ ys)).wt + 1)) :=
  FunAll.mono (append_spec h xs ys) fun w cost hw => ⟨hw.1, by rw [hw.1] at hw; exact hw.2⟩

end GI.Lang
