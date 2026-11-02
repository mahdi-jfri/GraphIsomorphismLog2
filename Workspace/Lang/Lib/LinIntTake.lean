import Workspace.Lang.Lib.LinIntTail

namespace GI.Lang
open GI.Cited (Val)

/-- Copy a prefix of a list of values. -/
def linTakeStep : Expr :=
  .snoc (arg 2) (.get (.get (arg 0) (.nat 1)) (arg 1))

def linTakeFuns (b : ℕ) : List Expr := loopFuns b (arg 0) .nil linTakeStep

def linTakeCost (W : ℕ) : ℕ := 10000 * (W + 1) ^ 3

theorem linTake_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linTakeFuns b))
    (xs : List Val) (k : ℕ) (hk : k ≤ xs.length) :
    FunDet P b (.list [.nat k, .list xs]) (.list (xs.take k))
      (linTakeCost (Val.list [.nat k, .list xs]).wt) := by
  let a := Val.list [.nat k, .list xs]
  let W := a.wt
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp)
  have hlen := length_lt_wt_list xs
  have hkw : k < W := lt_of_le_of_lt hk (hlen.trans wx)
  have hacc (i : ℕ) : (Val.list (xs.take i)).wt ≤ W :=
    (wt_list_sublist (List.take_sublist i xs)).trans wx.le
  have dk := Det.arg' (P := P) (vs := [.nat k, .list xs]) (rest := []) (j := 0) rfl
  have hlp : P.HasAt b (loopFuns b (arg 0) .nil linTakeStep) := hp
  have hloop := loopBdd_spec hlp dk Det.nil (by
    change 2 * W + 0 + 5 + 5 ≤ 10 * (W + k + 1)
    omega)
    (Inv := fun i acc => acc = .list (xs.take i)) (M := W) (D := fun _ => 1000 * (W + 1))
    (by simp) (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
    change cost ≤ k * (1000 * (W + 1)) + 1000 * (k + 1) * (W + k + W + 1) at hc
    unfold linTakeCost
    change cost ≤ 10000 * (W + 1) ^ 3
    nlinarith [Nat.pow_le_pow_right (by omega : 0 < W + 1) (by decide : 2 ≤ 3)]
  · subst acc
    have hi' : i < xs.length := hi.trans_le hk
    have dxs := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)]) (rest := []) (j := 0) rfl)
      (Det.nat 1) (show [Val.nat k, .list xs][1]? = some (.list xs) from rfl)
    have di := Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)]) (rest := []) (j := 1) rfl
    have dx := Det.get' dxs di (List.getElem?_eq_getElem hi')
    have da := Det.arg' (P := P) (vs := [a, .nat i, .list (xs.take i)]) (rest := []) (j := 2) rfl
    have dres := Det.snoc da dx
    have heq : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']; rfl
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list (xs.take i ++ [xs[i]]) = Val.list (xs.take (i + 1))
      rw [heq]
    · have wi := wt_nat_le i
      have ws := wt_list3_le a (.nat i) (.list (xs.take i))
      have wa := hacc i
      have wo := hacc (i + 1)
      rw [heq] at wo
      have wxi := wt_getElem_lt xs i hi'
      beta_reduce at hc ⊢
      change cost ≤ 1000 * (W + 1) + 100 * (W + k + W + 1)
      change (Val.list [a, .nat i, .list (xs.take i)]).wt ≤ 2 * (W + (Val.nat i).wt + (Val.list (xs.take i)).wt) + 7 at ws
      omega

/-- Prefix extraction of a finite-indexed list is restriction along Fin.castLE. -/
theorem linTakeFinMap {r c : ℕ} {α : Type*} (hcr : c ≤ r) (f : Fin r → α) :
    ((List.finRange r).map f).take c = (List.finRange c).map (fun i => f (Fin.castLE hcr i)) := by
  apply List.ext_getElem (by simp [Nat.min_eq_left hcr])
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_map, List.getElem_finRange]
  congr 1

theorem linTakeCost_mono {W V : ℕ} (h : W ≤ V) : linTakeCost W ≤ linTakeCost V := by
  unfold linTakeCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

end GI.Lang
