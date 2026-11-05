module

public import Workspace.Impl.TermJSolMath

@[expose] public section

/-!
# Dropping a prefix of a list (program)

`tmJSolDropFuns b` is a loop module: on `[k, xs]` it returns `xs.drop k`. We use it to read the
last `G` entries of a vector on `Fin (t + G)` (`tmJSolDrop_vec`) and the last `G` rows of a
matrix with `t + G` rows (`tmJSolDrop_rows`).
-/

namespace GI.Impl
open GI.Lang
open GI.Cited (Val encInt encIntMatrix)

/-- The step on `[[k, xs], i, acc]`: add `xs[k + i]` to the accumulator. -/
def tmJSolDropStep : Expr :=
  .snoc (arg 2) (.get (.get (arg 0) (.nat 1)) (.arith .add (.get (arg 0) (.nat 0)) (arg 1)))

/-- On `[k, xs]`: the list `xs.drop k`. -/
def tmJSolDropFuns (b : ℕ) : List Expr :=
  loopFuns b (.arith .sub (.length (.get (.var 0) (.nat 1))) (.get (.var 0) (.nat 0))) .nil
    tmJSolDropStep

theorem tmJSolDropFuns_length (b : ℕ) : (tmJSolDropFuns b).length = 3 := rfl

/-- The cost bound of the drop module. -/
def tmJSolDropCost (W : ℕ) : ℕ := 10000 * (W + 1) ^ 3

theorem tmJSolDropCost_mono {W V : ℕ} (h : W ≤ V) : tmJSolDropCost W ≤ tmJSolDropCost V := by
  unfold tmJSolDropCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

set_option maxHeartbeats 1000000 in
/-- **Drop.** On `[k, xs]` the module returns `xs.drop k`. -/
theorem tmJSolDrop_spec {P : Program} {b : ℕ} (hp : P.HasAt b (tmJSolDropFuns b))
    (k : ℕ) (xs : List Val) :
    FunDet P b (.list [.nat k, .list xs]) (.list (xs.drop k))
      (tmJSolDropCost (Val.list [.nat k, .list xs]).wt) := by
  let a := Val.list [.nat k, .list xs]
  let W := a.wt
  let n := xs.length - k
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < W := wt_le_wt_list (by simp)
  have hlen := length_lt_wt_list xs
  have wk := wt_nat_le k
  have hk := Det.arith (op := .sub)
    (Det.length (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1)
      (show [Val.nat k, .list xs][1]? = some (.list xs) from rfl)))
    (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 0)
      (show [Val.nat k, .list xs][0]? = some (.nat k) from rfl))
  have hwk : (Val.nat (xs.length - k)).wt ≤ xs.length + 2 := by
    have := wt_nat_le (xs.length - k); omega
  simp only [GI.Machine.BinOp.eval_sub] at hk
  have hacc (i : ℕ) : (Val.list ((xs.drop k).take i)).wt ≤ W :=
    (wt_list_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))).trans wx.le
  have hlp : P.HasAt b (loopFuns b (.arith .sub (.length (.get (.var 0) (.nat 1)))
      (.get (.var 0) (.nat 0))) .nil tmJSolDropStep) := hp
  have hloop := loopBdd_spec hlp hk Det.nil (by
    have hW := a.two_le_size.trans a.size_le_wt
    have haW : (Val.list [Val.nat k, Val.list xs]).wt = W := rfl
    change xs.length < (Val.list xs).wt at hlen
    omega)
    (Inv := fun i acc => acc = .list ((xs.drop k).take i)) (M := W) (D := fun _ => 1000 * (W + 1))
    (by simp) (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · have he := hw.1
      have hklen : n = (xs.drop k).length := by simp [n]
      change w = .list ((xs.drop k).take n) at he
      rw [hklen, List.take_length] at he
      exact he
    · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hw
      unfold tmJSolDropCost
      change cost ≤ 10000 * (W + 1) ^ 3
      have hcost := hw.2
      change cost ≤ n * (1000 * (W + 1)) + loopModK * (n + 1) * (W + n + W + 1) at hcost
      have hkw : n ≤ W := by
        change xs.length < (Val.list xs).wt at hlen
        omega
      simp only [loopModK] at hcost
      nlinarith [Nat.pow_le_pow_right (show 0 < W + 1 by omega) (show 2 ≤ 3 by decide)]
  · subst acc
    have hi' : k + i < xs.length := by omega
    have hx := List.getElem?_eq_getElem hi'
    let e := [a, Val.nat i, .list ((xs.drop k).take i)]
    have d0 := Det.arg' (P := P) (vs := e) (rest := []) (j := 0) rfl
    have dk := Det.get' d0 (Det.nat 0) (show [Val.nat k, .list xs][0]? = some (.nat k) from rfl)
    have dxs := Det.get' d0 (Det.nat 1) (show [Val.nat k, .list xs][1]? = some (.list xs) from rfl)
    have di := Det.arith (op := .add) dk (Det.arg' (P := P) (vs := e) (rest := []) (j := 1) rfl)
    have dx := Det.get' dxs di hx
    have da := Det.arg' (P := P) (vs := e) (rest := []) (j := 2) rfl
    have dres := Det.snoc da dx
    have heq : (xs.drop k).take (i + 1) = (xs.drop k).take i ++ [xs[k + i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
      simp [List.getElem_drop]
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list ((xs.drop k).take i ++ [xs[k + i]]) = Val.list ((xs.drop k).take (i + 1))
      rw [heq]
    · have wxi := wt_getElem_lt xs (k + i) hi'
      have wa := hacc i
      have wo := hacc (i + 1)
      rw [heq] at wo
      have wi := wt_nat_le i
      have wi1 := wt_nat_le (k + i)
      have ws := wt_list3_le a (.nat i) (.list ((xs.drop k).take i))
      have hiW : i < W := by
        change xs.length < (Val.list xs).wt at hlen
        omega
      beta_reduce at hc ⊢
      simp only [GI.Machine.BinOp.eval_add] at hc
      change cost ≤ 1000 * (W + 1) + 100 * (W + n + W + 1)
      change (Val.list e).wt ≤ 2 * (W + (Val.nat i).wt + (Val.list ((xs.drop k).take i)).wt) + 7
        at ws
      omega

/-- `finRange (t + G)` splits into the first `t` and the last `G` indices. -/
theorem tmJSol_map_finRange_add {α : Type*} {t G : ℕ} (f : Fin (t + G) → α) :
    (List.finRange (t + G)).map f =
      (List.finRange t).map (fun i => f (Fin.castAdd G i)) ++
        (List.finRange G).map (fun k => f (Fin.natAdd t k)) := by
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

/-- Dropping `t` entries of a vector on `Fin (t + G)` leaves its last `G` entries. -/
theorem tmJSolDrop_vec {t G : ℕ} (z : Fin (t + G) → ℤ) :
    ((List.finRange (t + G)).map fun i => encInt (z i)).drop t =
      (List.finRange G).map fun k => encInt (z (Fin.natAdd t k)) := by
  rw [tmJSol_map_finRange_add]
  exact List.drop_left' (by simp)

/-- Dropping `t` rows of a matrix with `t + G` rows leaves its last `G` rows. -/
theorem tmJSolDrop_rows {t G c : ℕ} (U : Matrix (Fin (t + G)) (Fin c) ℤ) :
    ((List.finRange (t + G)).map fun i => linVecVal (U i)).drop t =
      (List.finRange G).map fun k => linVecVal (U (Fin.natAdd t k)) := by
  rw [tmJSol_map_finRange_add]
  exact List.drop_left' (by simp)

/-- The drop module on a vector. -/
theorem tmJSolDrop_vec_spec {P : Program} {b : ℕ} (hp : P.HasAt b (tmJSolDropFuns b))
    {t G : ℕ} (z : Fin (t + G) → ℤ) :
    FunDet P b (.list [.nat t, linVecVal z]) (linVecVal fun k => z (Fin.natAdd t k))
      (tmJSolDropCost (Val.list [.nat t, linVecVal z]).wt) := by
  have h := tmJSolDrop_spec hp t ((List.finRange (t + G)).map fun i => encInt (z i))
  rw [tmJSolDrop_vec] at h
  exact h

end GI.Impl
