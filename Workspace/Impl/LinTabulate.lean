module

public import Workspace.Impl.LinMapEncoded
public import Workspace.Impl.LinSumPerm

@[expose] public section

/-! Enumerate a bounded coordinate interval and tabulate a scalar program.
The cost counts the interval length, as required for explicit dense matrices. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linTabulateF (range map : ℕ) : Expr :=
  .letE (.call range (arg 1)) (.call map (mk2 (arg 0) (.var 1)))

def linTabulateFuns (b f : ℕ) : List Expr :=
  [linTabulateF (b + 1) (b + 4)] ++ rangeFuns (b + 1) ++ mapFuns (b + 4) f

theorem linTabulateFuns_length (b f : ℕ) : (linTabulateFuns b f).length = 7 := rfl

structure linTabulateAt (P : Program) (b f : ℕ) : Prop where
  entry : P.funs[b]? = some (linTabulateF (b + 1) (b + 4))
  range : P.HasAt (b + 1) (rangeFuns (b + 1))
  map : P.HasAt (b + 4) (mapFuns (b + 4) f)

theorem linTabulateAt_of {P : Program} {b f : ℕ}
    (hp : P.HasAt b (linTabulateFuns b f)) : linTabulateAt P b f where
  entry := (hp.block (gs := [linTabulateF (b + 1) (b + 4)]) 0 rfl).single
  range := hp.block 1 rfl
  map := hp.block 4 rfl

def linTabulateRangeCost (n : ℕ) : ℕ :=
  10000 * (n + 1) * (4 * (n + 1) ^ 2 + n + 1)
def linTabulateCost (W n B : ℕ) : ℕ :=
  10000 * (W + n + linTabulateRangeCost n +
    linMapBudget (100 * (W + n + 1) ^ 2) B + 100 * (W + n + 1) ^ 2 + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linTabulate_spec {P : Program} {b f n : ℕ}
    (hp : linTabulateAt P b f) (c : Val) (F : Fin n → Val) (B : ℕ)
    (hf : ∀ i : Fin n, FunDet P f (.list [c, .nat i]) (F i) B) :
    FunDet P b (.list [c, .nat n]) (.list ((List.finRange n).map F))
      (linTabulateCost (Val.list [c, .nat n]).wt n B) := by
  let a := Val.list [c, .nat n]
  let W := a.wt
  let ids := encFun (fun i : Fin n => (i : ℕ))
  have wi : ids.wt ≤ 4 * (n + 1) ^ 2 := wt_ids_le n
  have wn := wt_nat_le n
  have wc : c.wt ≤ W := (wt_le_wt_list (by simp [W, a])).le
  have wr := range_spec hp.range n
  have wr' : FunDet P (b + 1) (.nat n) ids (linTabulateRangeCost n) := by
    refine wr.mono fun w cost hw => ⟨hw.1.trans range_eq_encPerm_one, ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    unfold linTabulateRangeCost
    change cost ≤ _
    change cost ≤ loopModK * (n + 1) * ((Val.nat n).wt + n + ids.wt + 1) at hc
    simp only [loopModK] at hc
    have hh : (Val.nat n).wt + n + ids.wt + 1 ≤ 10 * (4 * (n + 1) ^ 2 + n + 1) := by
      have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by decide) _
      omega
    calc cost ≤ 1000 * (n + 1) * ((Val.nat n).wt + n + ids.wt + 1) := hc
      _ ≤ 1000 * (n + 1) * (10 * (4 * (n + 1) ^ 2 + n + 1)) := Nat.mul_le_mul_left _ hh
      _ = _ := by ring
  have wm : (Val.list [c, ids]).wt ≤ 100 * (W + n + 1) ^ 2 := by
    have hh := wt_list2_le c ids
    have hp : (n + 1) ^ 2 ≤ (W + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hw : W ≤ (W + n + 1) ^ 2 := by nlinarith
    nlinarith
  have hm := linMapEncoded_spec hp.map (fun i : Fin n => Val.nat i)
    (fun i j h => Fin.ext (Val.nat.inj h)) F c (List.finRange n) B (fun i _ => hf i)
  have hm' := hm.mono (linMapBudget_mono wm le_rfl)
  have dr := Det.call (Det.arg' (P := P) (vs := [c, .nat n]) (rest := []) (j := 1) rfl) wr'
  have dm := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [c, .nat n]) (rest := [ids]) (j := 0) rfl)
    (Det.var' (P := P) (env := [a, ids]) (i := 1) rfl)) hm'
  apply FunDet.intro hp.entry
  refine (Det.letE dr dm).mono ?_
  have wo := hm'.wt_lt.le
  have wm' := wt_list2_le c ids
  have wip : ids.wt ≤ 100 * (W + n + 1) ^ 2 := by
    have hh : (n + 1) ^ 2 ≤ (W + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  change _ ≤ linTabulateCost W n B
  dsimp only [linTabulateCost]
  dsimp only [a, W, ids, encFun] at *
  omega

theorem linTabulateCost_mono {W V n m B C : ℕ} (hW : W ≤ V) (hn : n ≤ m) (hB : B ≤ C) :
    linTabulateCost W n B ≤ linTabulateCost V m C := by
  unfold linTabulateCost linTabulateRangeCost linMapBudget
  gcongr

theorem linTabulateCost_poly : PBU linTabulateCost := by
  unfold linTabulateCost linTabulateRangeCost linMapBudget
  norm_poly

end GI.Impl
