module

public import Workspace.Lang.Lib.LinIntVector

@[expose] public section

/-! Integer dot products. Partial sums are bounded by n times a product bound,
so the loop uses a polynomial bit bound rather than iterating a scalar cost bound. -/
namespace GI.Lang
open GI.Cited (Val encInt)

/-- The kth product, extended by zero beyond the row length. -/
def linDotTerm {n : ℕ} (x y : Fin n → ℤ) (k : ℕ) : ℤ :=
  if hk : k < n then x ⟨k, hk⟩ * y ⟨k, hk⟩ else 0

def linDotPartial {n : ℕ} (x y : Fin n → ℤ) (i : ℕ) : ℤ :=
  ∑ k ∈ Finset.range i, linDotTerm x y k

@[simp] theorem linDotPartial_zero {n : ℕ} (x y : Fin n → ℤ) : linDotPartial x y 0 = 0 := by
  simp [linDotPartial]

theorem linDotPartial_step {n : ℕ} (x y : Fin n → ℤ) (i : ℕ) (hi : i < n) :
    linDotPartial x y (i + 1) = linDotPartial x y i + x ⟨i, hi⟩ * y ⟨i, hi⟩ := by
  simp [linDotPartial, Finset.sum_range_succ, linDotTerm, hi]

theorem linDotPartial_full {n : ℕ} (x y : Fin n → ℤ) : linDotPartial x y n = ∑ i, x i * y i := by
  rw [linDotPartial, ← Fin.sum_univ_eq_sum_range]
  simp [linDotTerm]

/-- A uniform polynomial bit-weight bound for every partial sum. -/
theorem linDotPartial_wt {n : ℕ} (x y : Fin n → ℤ) (W : ℕ)
    (hx : ∀ j, (encInt (x j)).wt ≤ W) (hy : ∀ j, (encInt (y j)).wt ≤ W)
    (i : ℕ) (hi : i ≤ n) : (encInt (linDotPartial x y i)).wt ≤ 20 * (n + 2 * W + 2) := by
  apply linWtInt (B := n + 2 * W + 1)
  have ht (k : ℕ) : (linDotTerm x y k).natAbs ≤ 2 ^ (2 * W) := by
    unfold linDotTerm
    split_ifs with hk
    · rw [Int.natAbs_mul, show 2 * W = W + W by omega, pow_add]
      have hxa := (linEncIntAbs (x ⟨k, hk⟩)).trans_le (Nat.pow_le_pow_right (by decide) (hx _))
      have hya := (linEncIntAbs (y ⟨k, hk⟩)).trans_le (Nat.pow_le_pow_right (by decide) (hy _))
      exact (Nat.mul_lt_mul'' hxa hya).le
    · simp
  have hs := (Int.natAbs_sum_le (Finset.range i) (linDotTerm x y)).trans
    (Finset.sum_le_sum (fun k _ => ht k))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hn : i ≤ 2 ^ n := hi.trans Nat.lt_two_pow_self.le
  have hm := Nat.mul_le_mul_right (2 ^ (2 * W)) hn
  rw [← pow_add] at hm
  have hp : 2 ^ (n + 2 * W) < 2 ^ (n + 2 * W + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact (hs.trans hm).trans_lt hp

/-- One multiply-add step on [context,index,partial sum]. -/
def linDotStep (ib : ℕ) : Expr :=
  .letE (.call (ib + 13) (mk2
    (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1))))
    (.call (ib + 11) (mk2 (arg 2) (.var 1)))

/-- The third input is the zero accumulator. The wrapper below supplies it. -/
def linDotLoopFuns (b ib : ℕ) : List Expr :=
  loopFuns b (.length (arg 0)) (arg 2) (linDotStep ib)

def linDotAccWt (W n : ℕ) : ℕ := 20 * (n + 2 * W + 2)
def linDotProductWt (W : ℕ) : ℕ := 20 * (2 * W + 1)

def linDotStepCost (W n : ℕ) : ℕ :=
  linIntBinaryCost (4 * W + 6) +
    linIntBinaryCost (2 * (linDotAccWt W n + linDotProductWt W) + 6) +
    1000 * (W + n + linDotAccWt W n + linDotProductWt W + 1)

def linDotLoopCost (W n : ℕ) : ℕ :=
  n * linDotStepCost W n + loopModK * (n + 1) * (W + n + linDotAccWt W n + 1)

set_option maxHeartbeats 2000000 in
/-- The dot-product loop returns the exact sum with a polynomial bit cost. -/
theorem linDotLoop_spec {P : Program} {b ib n : ℕ} (h : linIntSpec P ib)
    (hp : P.HasAt b (linDotLoopFuns b ib)) (x y : Fin n → ℤ) :
    FunDet P b (.list [linVecVal x, linVecVal y, encInt 0]) (encInt (∑ j, x j * y j))
      (linDotLoopCost (Val.list [linVecVal x, linVecVal y, encInt 0]).wt n) := by
  let a := Val.list [linVecVal x, linVecVal y, encInt 0]
  let M := linDotAccWt a.wt n
  let B := linDotProductWt a.wt
  have wx : (linVecVal x).wt < a.wt := wt_le_wt_list (by simp)
  have wy : (linVecVal y).wt < a.wt := wt_le_wt_list (by simp)
  have hacc (i : ℕ) (hi : i ≤ n) : (encInt (linDotPartial x y i)).wt ≤ M :=
    linDotPartial_wt x y a.wt (fun j => ((linVecEntryWt x j).trans wx).le)
      (fun j => ((linVecEntryWt y j).trans wy).le) i hi
  have dk := Det.length (Det.arg' (P := P) (vs := [linVecVal x, linVecVal y, encInt 0])
    (rest := []) (j := 0) rfl)
  simp only [List.length_map, List.length_finRange] at dk
  have dz := Det.arg' (P := P) (vs := [linVecVal x, linVecVal y, encInt 0]) (rest := []) (j := 2) rfl
  have hlp : P.HasAt b (loopFuns b (.length (arg 0)) (arg 2) (linDotStep ib)) := hp
  have hloop := loopBdd_spec hlp dk dz (by
    change (2 * a.wt + 0 + 5 + n + 3) + (2 * a.wt + 2 + 5) ≤ 10 * (a.wt + n + 1)
    have := a.two_le_size.trans a.size_le_wt
    omega)
    (Inv := fun i acc => acc = encInt (linDotPartial x y i)) (M := M)
    (D := fun _ => linDotStepCost a.wt n) (by simp)
    (fun i acc hi he => he ▸ hacc i hi) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · simpa [linDotPartial_full] using hw.1
    · simpa [linDotLoopCost, M, a, Finset.sum_const, Finset.card_range, smul_eq_mul] using hw.2
  · subst acc
    let j : Fin n := ⟨i, hi⟩
    let env := [Val.list [a, .nat i, encInt (linDotPartial x y i)]]
    have dax := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, encInt (linDotPartial x y i)])
      (rest := []) (j := 0) rfl) (Det.nat 0) (show [linVecVal x, linVecVal y, encInt 0][0]? = _ from rfl)
    have day := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, encInt (linDotPartial x y i)])
      (rest := []) (j := 0) rfl) (Det.nat 1) (show [linVecVal x, linVecVal y, encInt 0][1]? = _ from rfl)
    have di := Det.arg' (P := P) (vs := [a, .nat i, encInt (linDotPartial x y i)]) (rest := []) (j := 1) rfl
    have hget : (List.finRange n)[i]? = some j := by
      rw [List.getElem?_eq_getElem (by simpa using hi)]; simp [j]
    have dx := Det.get' dax di (by rw [List.getElem?_map, hget]; rfl)
    have dy := Det.get' day di (by rw [List.getElem?_map, hget]; rfl)
    have dp := Det.call (Det.mk2 dx dy) (h.mul (x j) (y j))
    have da := Det.arg' (P := P) (vs := [a, .nat i, encInt (linDotPartial x y i)])
      (rest := [encInt (x j * y j)]) (j := 2) rfl
    have dv := Det.var' (P := P)
      (env := env ++ [encInt (x j * y j)]) (i := 1) rfl
    have ds := Det.call (Det.mk2 da dv) (h.add (linDotPartial x y i) (x j * y j))
    have dres := Det.letE dp ds
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change encInt (linDotPartial x y i + x j * y j) = encInt (linDotPartial x y (i + 1))
      rw [linDotPartial_step x y i hi]
    · have wxj := (linVecEntryWt x j).trans wx
      have wyj := (linVecEntryWt y j).trans wy
      have wp : (encInt (x j * y j)).wt ≤ B := linEncIntMulWt _ _ _ wxj.le wyj.le
      have wa := hacc i hi.le
      have wr := hacc (i + 1) hi
      rw [linDotPartial_step x y i hi] at wr
      change (encInt (linDotPartial x y i + x j * y j)).wt ≤ M at wr
      have wi := wt_nat_le i
      have wenv := wt_list3_le a (.nat i) (encInt (linDotPartial x y i))
      have wmul := wt_list2_le (encInt (x j)) (encInt (y j))
      have wadd := wt_list2_le (encInt (linDotPartial x y i)) (encInt (x j * y j))
      have hmc := linIntBinaryCost_mono (show (Val.list [encInt (x j), encInt (y j)]).wt ≤ 4 * a.wt + 6 by omega)
      have hac := linIntBinaryCost_mono
        (show (Val.list [encInt (linDotPartial x y i), encInt (x j * y j)]).wt ≤ 2 * (M + B) + 6 by omega)
      beta_reduce at hc ⊢
      change cost ≤ linDotStepCost a.wt n + 100 * (a.wt + n + M + 1)
      change _ ≤ _ at hc
      change (linVecVal x).wt < a.wt at wx
      change (linVecVal y).wt < a.wt at wy
      unfold linDotStepCost
      change cost ≤ _
      have hM : linDotAccWt a.wt n = M := rfl
      have hB : linDotProductWt a.wt = B := rfl
      rw [hM, hB]
      change _ ≤ _ at hc
      omega

/-- The loop cost increases with the bit weight of its input. -/
theorem linDotLoopCost_mono {W V : ℕ} (h : W ≤ V) (n : ℕ) : linDotLoopCost W n ≤ linDotLoopCost V n := by
  have hm : linDotAccWt W n ≤ linDotAccWt V n := by unfold linDotAccWt; omega
  have hp : linDotProductWt W ≤ linDotProductWt V := by unfold linDotProductWt; omega
  have hc1 := linIntBinaryCost_mono (show 4 * W + 6 ≤ 4 * V + 6 by omega)
  have hc2 := linIntBinaryCost_mono (show 2 * (linDotAccWt W n + linDotProductWt W) + 6 ≤
    2 * (linDotAccWt V n + linDotProductWt V) + 6 by omega)
  have hs : linDotStepCost W n ≤ linDotStepCost V n := by unfold linDotStepCost; omega
  unfold linDotLoopCost
  exact Nat.add_le_add (Nat.mul_le_mul_left n hs)
    (Nat.mul_le_mul_left _ (by omega))

end GI.Lang
