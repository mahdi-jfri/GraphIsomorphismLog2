module

public import Workspace.Impl.LinTrialPrimary
public import Workspace.Impl.LinLoopInit

@[expose] public section

/-! Repeated trial division of one positive cyclic order. -/
namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (len len_mono BinOp)

def linTrialPrimaryVal (z : ℕ × ℕ) : Val := .list [.nat z.1, .nat z.2]

def linTrialPrimaryStep : Expr :=
  .ite (.arith .eq (.arith .mod (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 0))) (.nat 0))
    (mk2 (.arith .add (.get (arg 2) (.nat 0)) (.nat 1))
      (.arith .div (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 0))))
    (arg 2)

def linTrialPrimaryFuns (b : ℕ) : List Expr :=
  loopFuns b (arg 2) (mk2 (.nat 0) (arg 1)) linTrialPrimaryStep

theorem linTrialPrimaryFuns_length (b : ℕ) : (linTrialPrimaryFuns b).length = 3 := rfl

def linTrialPrimaryCost (W k : ℕ) : ℕ := 10000000 * (k + 1) * (W + k + 1)

theorem linTrialPrimary_cofactor_le (p n k : ℕ) : (linTrialPrimary p n k).2 ≤ n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [linTrialPrimary]
    split_ifs
    · exact (Nat.div_le_self _ _).trans ih
    · exact ih

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linTrialPrimaryProg_spec {P : Program} {b : ℕ}
    (h : P.HasAt b (linTrialPrimaryFuns b)) (p n k : ℕ) (hp : 2 ≤ p) (hn : 0 < n) :
    FunDet P b (.list [.nat p, .nat n, .nat k])
      (linTrialPrimaryVal (linTrialPrimary p n k))
      (linTrialPrimaryCost (Val.list [.nat p, .nat n, .nat k]).wt k) := by
  let a := Val.list [.nat p, .nat n, .nat k]
  let W := a.wt
  let M := 100 * (W + k + 1)
  have wn : (Val.nat n).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [a, W])
  have wi (j : ℕ) (hj : j ≤ k) : (Val.nat (linTrialPrimary p n j).1).wt ≤ k + 3 := by
    have he := (linTrialPrimary_invariant p n hp hn j).2.2.1
    exact (wt_nat_le _).trans (by omega)
  have wc (j : ℕ) : (Val.nat (linTrialPrimary p n j).2).wt ≤ W := by
    rw [wt_nat] at *
    have hh := len_mono (linTrialPrimary_cofactor_le p n j)
    omega
  have wacc (j : ℕ) (hj : j ≤ k) : (linTrialPrimaryVal (linTrialPrimary p n j)).wt ≤ M := by
    have hh := wt_list2_le (.nat (linTrialPrimary p n j).1) (.nat (linTrialPrimary p n j).2)
    have := wi j hj
    have := wc j
    dsimp only [linTrialPrimaryVal, M]
    omega
  have dk := Det.arg' (P := P) (vs := [.nat p, .nat n, .nat k]) (rest := []) (j := 2) rfl
  have dn := Det.arg' (P := P) (vs := [.nat p, .nat n, .nat k]) (rest := []) (j := 1) rfl
  have hl := linLoopBddInit_spec h dk (Det.mk2 (Det.nat 0) dn)
    (Inv := fun j acc => acc = linTrialPrimaryVal (linTrialPrimary p n j))
    (M := M) (D := fun _ => 10000 * (W + k + M + 1)) rfl
    (fun j acc hj he => he ▸ wacc j hj) (fun j acc hj he => ?_)
  · refine hl.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
    change cost ≤ linTrialPrimaryCost W k
    unfold linTrialPrimaryCost
    have hh := Nat.mul_le_mul_right (10000 * (W + k + M + 1)) (Nat.le_succ k)
    have winit := wt_list2_le (.nat 0) (.nat n)
    have wz : (Val.nat 0).wt = 2 := rfl
    have wn' : (Val.nat n).wt < (Val.list [.nat p, .nat n, .nat k]).wt := wn
    change cost ≤ _ at hc
    change _ ≤ _ at hh
    have hc' : cost ≤ 12000 * (k + 1) * (W + k + M + 1) := by
      dsimp only [W, a] at *
      nlinarith only [hc, hh, winit, wz, wn']
    dsimp only [M] at hc'
    nlinarith only [hc']
  · subst acc
    let z := linTrialPrimary p n j
    have wz := wacc j hj.le
    have we := wi j hj.le
    have wco := wc j
    have we' := wi (j + 1) (by omega)
    have wco' := wc (j + 1)
    have de := Det.get' (Det.arg' (P := P) (vs := [a, .nat j, linTrialPrimaryVal z])
      (rest := []) (j := 2) rfl) (Det.nat 0) rfl
    have dc := Det.get' (Det.arg' (P := P) (vs := [a, .nat j, linTrialPrimaryVal z])
      (rest := []) (j := 2) rfl) (Det.nat 1) rfl
    have dp := Det.get' (Det.arg' (P := P) (vs := [a, .nat j, linTrialPrimaryVal z])
      (rest := []) (j := 0) rfl) (Det.nat 0) rfl
    have dmod := Det.arith (op := .mod) dc dp
    have wmod : (Val.nat (z.2 % p)).wt ≤ (Val.nat z.2).wt := by
      simp only [wt_nat]
      exact Nat.add_le_add_right (len_mono (Nat.mod_le _ _)) 2
    have wenv := wt_list3_le a (.nat j) (linTrialPrimaryVal z)
    have wj := wt_nat_le j
    by_cases hd : p ∣ z.2
    · have hz : z.2 % p = 0 := Nat.mod_eq_zero_of_dvd hd
      have dtest := Det.arith' (op := .eq) dmod (Det.nat 0)
        (z := 1) (by simp [BinOp.eval, hz])
      have dout := Det.mk2 (Det.arith (op := .add) de (Det.nat 1))
        (Det.arith (op := .div) dc dp)
      have d := Det.ite_pos (e := arg 2) dtest (by decide : 1 ≠ 0) dout
      have hnext : linTrialPrimary p n (j + 1) = (z.1 + 1, z.2 / p) := by
        simp only [linTrialPrimary, show linTrialPrimary p n j = z from rfl, if_pos hd]
      rw [hnext] at we' wco'
      refine d.post fun cost hc => ⟨?_, ?_⟩
      · simp only [BinOp.eval_add, BinOp.eval_div, linTrialPrimaryVal, hnext]
      · have wout := wt_list2_le (.nat (z.1 + 1)) (.nat (z.2 / p))
        simp only [BinOp.eval_add, BinOp.eval_div, BinOp.eval_mod] at hc
        change cost ≤ 10000 * (W + k + M + 1) + 100 * (W + k + M + 1)
        dsimp only [linTrialPrimaryVal, z] at *
        omega
    · have hz : z.2 % p ≠ 0 := fun hz => hd (Nat.dvd_of_mod_eq_zero hz)
      have dtest := Det.arith' (op := .eq) dmod (Det.nat 0)
        (z := 0) (by simp [BinOp.eval, hz])
      have dout := Det.arg' (P := P) (vs := [a, .nat j, linTrialPrimaryVal z])
        (rest := []) (j := 2) rfl
      have d := Det.ite_zero (t := mk2 (.arith .add (.get (arg 2) (.nat 0)) (.nat 1))
        (.arith .div (.get (arg 2) (.nat 1)) (.get (arg 0) (.nat 0)))) dtest dout
      refine d.post fun cost hc => ⟨?_, ?_⟩
      · simp only [linTrialPrimary, show linTrialPrimary p n j = z from rfl, if_neg hd]
      · simp only [BinOp.eval_mod] at hc
        change cost ≤ 10000 * (W + k + M + 1) + 100 * (W + k + M + 1)
        dsimp only [linTrialPrimaryVal, z] at *
        omega

theorem linTrialPrimaryCost_poly : PBU (fun k W _ => linTrialPrimaryCost W k) := by
  unfold linTrialPrimaryCost
  norm_poly

end GI.Impl
