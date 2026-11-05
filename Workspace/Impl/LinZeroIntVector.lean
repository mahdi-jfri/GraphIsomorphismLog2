module

public import Workspace.Impl.LinMapSource
public import Workspace.Impl.LinPrimaryRecord
public import Workspace.Lang.Lib.Search

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linZeroIntPred (v : Val) : Bool := by
  classical
  exact decide (v = encInt 0)
def linZeroIntCellF : Expr := .arith .eq (.length (.get (arg 1) (.nat 1))) (.nat 0)

def linZeroIntVectorF (all : ℕ) : Expr := .call all (mk2 .nil (.var 0))
def linZeroIntVectorFuns (b : ℕ) : List Expr :=
  [linZeroIntVectorF (b + 1)] ++ allFuns (b + 1) (b + 4) ++ [linZeroIntCellF]

theorem linZeroIntVectorFuns_length (b : ℕ) : (linZeroIntVectorFuns b).length = 5 := rfl

structure linZeroIntVectorAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linZeroIntVectorF (b + 1))
  all : P.HasAt (b + 1) (allFuns (b + 1) (b + 4))
  cell : P.funs[b + 4]? = some linZeroIntCellF

theorem linZeroIntVectorAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linZeroIntVectorFuns b)) : linZeroIntVectorAt P b where
  entry := (h.block (gs := [linZeroIntVectorF (b + 1)]) 0 rfl).single
  all := h.block 1 rfl
  cell := (h.block (gs := [linZeroIntCellF]) 4 rfl).single

set_option maxHeartbeats 1000000 in
theorem linZeroIntCell_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some linZeroIntCellF)
    (ctx : Val) (z : ℤ) :
    FunDet P f (.list [ctx, encInt z]) (boolVal (linZeroIntPred (encInt z)))
      (1000 * ((Val.list [ctx, encInt z]).wt + 1)) := by
  classical
  let a := Val.list [ctx, encInt z]
  have dz := Det.arg' (P := P) (vs := [ctx, encInt z]) (rest := []) (j := 1) rfl
  have db := Det.get' dz (Det.nat 1) rfl
  have dl := Det.length db
  have dd := Det.arith (op := .eq) dl (Det.nat 0)
  simp only [List.length_map] at dd
  have wz : (encInt z).wt < a.wt := wt_le_wt_list (by simp [a])
  have wb : (linBitsVal z.natAbs.bits).wt < (encInt z).wt := wt_le_wt_list (by simp [encInt, linBitsVal, linBit])
  have hl : z.natAbs.bits.length < (linBitsVal z.natAbs.bits).wt := by
    have hh := length_lt_wt_list (z.natAbs.bits.map fun b => Val.nat (linBit b))
    simpa only [linBitsVal, List.length_map] using hh
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  apply FunDet.intro hf
  by_cases hz : z = 0
  · have he : linZeroIntPred (encInt z) = true := by simp [linZeroIntPred, hz]
    have hh : z.natAbs.bits.length = 0 := (linIntBits_zero_iff z).mpr hz
    refine dd.post fun cost hc => ⟨?_, ?_⟩
    · simp only [GI.Machine.BinOp.eval_eq, he, hh, boolVal]
      rfl
    · simp only [GI.Machine.BinOp.eval_eq, hh, if_true, if_false] at hc
      change cost ≤ 1000 * (a.wt + 1)
      dsimp only [a, linBitsVal, linBit] at *
      omega
  · have he : linZeroIntPred (encInt z) = false := by
      simp only [linZeroIntPred, decide_eq_false_iff_not]
      exact fun h => hz (encInt_injective h)
    have hh : z.natAbs.bits.length ≠ 0 := fun h => hz ((linIntBits_zero_iff z).mp h)
    refine dd.post fun cost hc => ⟨?_, ?_⟩
    · simp only [GI.Machine.BinOp.eval_eq, he, hh, boolVal]
      rfl
    · simp only [GI.Machine.BinOp.eval_eq, List.length_map, hh, if_true, if_false] at hc
      change cost ≤ 1000 * (a.wt + 1)
      dsimp only [a, linBitsVal, linBit] at *
      omega

def linZeroIntVectorCost (W : ℕ) : ℕ := 10000000 * (W + 1) ^ 3

set_option maxHeartbeats 1000000 in
theorem linZeroIntVector_spec {P : Program} {b d : ℕ} (h : linZeroIntVectorAt P b)
    (x : Fin d → ℤ) :
    FunDet P b (linVecVal x) (boolVal (decide (x = 0))) (linZeroIntVectorCost (linVecVal x).wt) := by
  classical
  let xs := (List.finRange d).map fun i => encInt (x i)
  let a := linVecVal x
  let W := a.wt
  have hd : d ≤ W := by
    have hh := length_lt_wt_list xs
    simpa only [xs, W, a, linVecVal, List.length_map, List.length_finRange] using hh.le
  have wa : (Val.list [.list [], a]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.list []) a
    have he : (Val.list []).wt = 4 := rfl
    dsimp only [W]
    omega
  have hcell : ∀ v ∈ xs, FunDet P (b + 4) (.list [.list [], v]) (boolVal (linZeroIntPred v)) (1000000 * (W + 1)) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have wi : (encInt (x i)).wt < W := linVecEntryWt x i
    have hh := wt_list2_le (.list []) (encInt (x i))
    have he : (Val.list []).wt = 4 := rfl
    exact (linZeroIntCell_spec h.cell (.list []) (x i)).mono (by omega)
  have heq : xs.all linZeroIntPred = decide (x = 0) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    constructor
    · intro hh
      funext i
      have hi := hh (encInt (x i)) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      simp only [linZeroIntPred, decide_eq_true_eq] at hi
      exact encInt_injective hi
    · intro hx v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      simp [linZeroIntPred, hx]
  have hall : FunDet P (b + 1) (.list [.list [], a]) (boolVal (decide (x = 0)))
      (2000000 * (W + 1) ^ 3) := by
    have hs := GI.Lang.all_spec h.all (q := linZeroIntPred) (B := fun _ => 1000000 * (W + 1)) hcell
    rw [heq] at hs
    refine hs.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [List.map_const', List.sum_replicate, xs, List.length_map, List.length_finRange, smul_eq_mul] at hc
    change cost ≤ d * (1000000 * (W + 1)) +
      loopModK * (d + 1) * ((Val.list [.list [], a]).wt + d + 4) at hc
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul_left loopModK (Nat.add_le_add_right hd 1))
      (show (Val.list [.list [], a]).wt + d + 4 ≤ 100 * (W + 1) + W + 4 by omega)
    have hp := Nat.mul_le_mul_right (1000000 * (W + 1)) hd
    unfold loopModK at hc hh
    nlinarith only [hc, hh, hp]
  have da := Det.mk2 (Det.nil (P := P) (env := [a])) (Det.var' (P := P) (env := [a]) (i := 0) rfl)
  have dd := Det.call da hall
  have wo := wt_boolVal_le (decide (x = 0))
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have hpow := Nat.le_self_pow (by decide : 3 ≠ 0) (W + 1)
  unfold linZeroIntVectorCost
  dsimp only [W, a] at *
  nlinarith only [wa, wo, hpow]

end GI.Impl
