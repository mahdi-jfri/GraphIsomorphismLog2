module

public import Workspace.Impl.LinMapEncoded

@[expose] public section

/-! A bounded product loop for p^j. The cost is polynomial in j and the bit
weight of the input; primary-layer indices are bounded by the stored bit data. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len len_pow_le)

def linNatPowerStep : Expr := .arith .mul (arg 2) (.get (arg 0) (.nat 0))
def linNatPowerFuns (b : ℕ) : List Expr := loopFuns b (arg 1) (.nat 1) linNatPowerStep

theorem linNatPowerFuns_length (b : ℕ) : (linNatPowerFuns b).length = 3 := rfl

def linNatPowerCost (W j : ℕ) : ℕ := 100000 * (j + 1) * (W + j + j * W + 4)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linNatPower_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linNatPowerFuns b)) (p j : ℕ) :
    FunDet P b (.list [.nat p, .nat j]) (.nat (p ^ j))
      (linNatPowerCost (Val.list [.nat p, .nat j]).wt j) := by
  let a := Val.list [.nat p, .nat j]
  let W := a.wt
  let M := j * W + 3
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W, a])
  have wlen : len p ≤ W := by rw [wt_nat] at wp; omega
  have wacc (k : ℕ) (hk : k ≤ j) : (Val.nat (p ^ k)).wt ≤ M := by
    rw [wt_nat]
    have hh := len_pow_le p k
    have hm := Nat.mul_le_mul hk wlen
    dsimp only [M]
    omega
  have dj := Det.arg' (P := P) (vs := [.nat p, .nat j]) (rest := []) (j := 1) rfl
  have hlp := loopBdd_spec hp dj (Det.nat 1) (by
    have hw := a.two_le_size.trans a.size_le_wt
    change 2 * a.wt + 1 + 5 + 4 ≤ 10 * (a.wt + j + 1)
    omega)
    (Inv := fun k acc => acc = .nat (p ^ k)) (M := M)
    (D := fun _ => 1000 * (W + j + M + 1)) (by simp)
    (fun k acc hk he => he ▸ wacc k hk) (fun k acc hk he => ?_)
  · refine hlp.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
    change cost ≤ linNatPowerCost W j
    unfold linNatPowerCost
    change cost ≤ j * (1000 * (W + j + M + 1)) +
      1000 * (j + 1) * (W + j + M + 1) at hc
    have hh := Nat.mul_le_mul_right (1000 * (W + j + M + 1)) (Nat.le_succ j)
    have hsum : cost ≤ 2000 * (j + 1) * (W + j + M + 1) := by nlinarith only [hc, hh]
    dsimp only [M] at hsum
    exact hsum.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2000 ≤ 100000)))
  · subst acc
    have wk := wacc k hk.le
    have wk' := wacc (k + 1) (by omega)
    have dctx := Det.arg' (P := P) (vs := [a, .nat k, .nat (p ^ k)]) (rest := []) (j := 0) rfl
    have dp := Det.get' dctx (Det.nat 0) rfl
    have da := Det.arg' (P := P) (vs := [a, .nat k, .nat (p ^ k)]) (rest := []) (j := 2) rfl
    have dd := Det.arith (op := .mul) da dp
    refine dd.post fun cost hc => ⟨?_, ?_⟩
    · simp only [GI.Machine.BinOp.eval_mul, pow_succ]
    · have wi := wt_nat_le k
      have warg := wt_list3_le a (.nat k) (.nat (p ^ k))
      simp only [GI.Machine.BinOp.eval_mul, ← pow_succ] at hc
      change cost ≤ 1000 * (W + j + M + 1) + 100 * (W + j + M + 1)
      change (Val.nat (p ^ k)).wt ≤ M at wk
      change (Val.nat (p ^ (k + 1))).wt ≤ M at wk'
      change cost ≤ _ at hc
      change (Val.list [a, .nat k, .nat (p ^ k)]).wt ≤ _ at warg
      omega

theorem linNatPowerCost_poly : PBU (fun j W _ => linNatPowerCost W j) := by
  unfold linNatPowerCost
  norm_poly

end GI.Impl
