module

public import Workspace.Lang.Lib.LinIntBits

@[expose] public section

/-! Conversion between the cited sign/bits integer encoding and a canonical pair
of natural positive and negative parts. Natural parts support the arithmetic
operations without branching on every integer constructor. -/
namespace GI.Lang
open GI.Cited (Val encInt)
open GI.Machine (len len_add_le)

/-- Canonical natural parts: z = positive - negative, with at least one part zero. -/
def linIntParts (z : ℤ) : Val := .list [.nat z.toNat, .nat (-z).toNat]

theorem linIntAbsParts (z : ℤ) : z.natAbs = z.toNat + (-z).toNat := by
  cases z <;> simp

theorem linIntParts_sign (z : ℤ) : linIntParts z =
    if z < 0 then .list [.nat 0, .nat z.natAbs] else .list [.nat z.natAbs, .nat 0] := by
  cases z <;> simp [linIntParts]

/-- A uniform cubic cost for either codec, in input bit weight. -/
def linIntCodecCost (W : ℕ) : ℕ := 10 ^ 6 * (W + 1) ^ 3

/-- Decode the magnitude, then put it in the positive or negative part. -/
def linIntDecodeF (bits : ℕ) : Expr :=
  .letE (.call bits (mk2 (arg 1) (.nat 0)))
    (.ite (arg 0) (mk2 (.nat 0) (.var 1)) (mk2 (.var 1) (.nat 0)))

/-- Encode the sum of the parts as a magnitude and test whether the negative part is nonzero. -/
def linIntEncodeF (bits : ℕ) : Expr :=
  mk2 (.arith .lt (.nat 0) (arg 1))
    (.call bits (mk2 (.arith .add (arg 0) (arg 1)) .nil))

/-- Decode a cited integer value into its canonical natural parts. -/
theorem linIntDecode_spec {P : Program} {f bits : ℕ}
    (hf : P.funs[f]? = some (linIntDecodeF bits))
    (hb : P.funs[bits]? = some (linBitsDecodeF bits)) (z : ℤ) :
    FunDet P f (encInt z) (linIntParts z) (linIntCodecCost (encInt z).wt) := by
  let s := if z < 0 then 1 else 0
  have hzv : encInt z = .list [.nat s, linBitsVal z.natAbs.bits] := rfl
  have dB := Det.arg' (P := P) (vs := [.nat s, linBitsVal z.natAbs.bits])
    (rest := []) (j := 1) rfl
  have dC := Det.call (Det.mk2 dB (Det.nat 0)) (linBitsDecode_spec hb z.natAbs.bits 0 (by omega))
  simp only [List.drop_zero, linBitsNat_bits] at dC
  have dS := Det.arg' (P := P) (vs := [.nat s, linBitsVal z.natAbs.bits])
    (rest := [.nat z.natAbs]) (j := 0) rfl
  have dM := Det.var' (P := P)
    (env := [.list [.nat s, linBitsVal z.natAbs.bits], .nat z.natAbs]) (i := 1) rfl
  have wM : (Val.nat z.natAbs).wt = z.natAbs.bits.length + 2 := by rw [wt_nat, linLenBits]
  have wS : (Val.nat s).wt ≤ 3 := by dsimp [s]; split_ifs <;> decide
  have wB := linBitsVal_wt z.natAbs.bits
  have wI := wt_list2_le (linBitsVal z.natAbs.bits) (.nat 0)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have wbits : z.natAbs.bits.length < (encInt z).wt := by
    have hl := length_lt_wt_list (z.natAbs.bits.map fun b => Val.nat (linBit b))
    have hw := wt_le_wt_list (vs := [.nat s, linBitsVal z.natAbs.bits])
      (v := linBitsVal z.natAbs.bits) (by simp)
    simp only [List.length_map] at hl
    rw [hzv]
    exact lt_trans hl hw
  have wm0 := wt_list2_le (.nat z.natAbs) (.nat 0)
  have w0m := wt_list2_le (.nat 0) (.nat z.natAbs)
  rw [hzv, linIntParts_sign]
  by_cases hneg : z < 0
  · rw [if_pos hneg]
    have ds : s ≠ 0 := by simp [s, hneg]
    apply FunDet.intro hf
    refine (Det.letE dC (Det.ite_pos dS ds (Det.mk2 (Det.nat 0) dM))).mono ?_
    unfold linIntCodecCost linBitsDecodeCost
    rw [hzv] at wbits
    simp only [Nat.sub_zero]
    nlinarith [Nat.pow_le_pow_left (show z.natAbs.bits.length + 1 ≤
      (Val.list [.nat s, linBitsVal z.natAbs.bits]).wt + 1 by omega) 3,
      Nat.le_self_pow (by decide : 3 ≠ 0) ((Val.list [.nat s, linBitsVal z.natAbs.bits]).wt + 1)]
  · rw [if_neg hneg]
    have hs : s = 0 := by simp [s, hneg]
    simp only [s, if_neg hneg] at *
    apply FunDet.intro hf
    refine (Det.letE dC (Det.ite_zero dS (Det.mk2 dM (Det.nat 0)))).mono ?_
    unfold linIntCodecCost linBitsDecodeCost
    rw [hzv] at wbits
    simp only [Nat.sub_zero]
    nlinarith [Nat.pow_le_pow_left (show z.natAbs.bits.length + 1 ≤
      (Val.list [.nat 0, linBitsVal z.natAbs.bits]).wt + 1 by omega) 3,
      Nat.le_self_pow (by decide : 3 ≠ 0) ((Val.list [.nat 0, linBitsVal z.natAbs.bits]).wt + 1)]

/-- Convert canonical natural parts back into the exact encInt format. -/
theorem linIntEncode_spec {P : Program} {f bits : ℕ}
    (hf : P.funs[f]? = some (linIntEncodeF bits))
    (hb : P.funs[bits]? = some (linBitsEncodeF bits)) (z : ℤ) :
    FunDet P f (linIntParts z) (encInt z) (linIntCodecCost (linIntParts z).wt) := by
  have dP := Det.arg' (P := P) (vs := [.nat z.toNat, .nat (-z).toNat]) (rest := []) (j := 0) rfl
  have dN := Det.arg' (P := P) (vs := [.nat z.toNat, .nat (-z).toNat]) (rest := []) (j := 1) rfl
  have dA := Det.arith (op := .add) dP dN
  have dS := Det.arith (op := .lt) (Det.nat 0) dN
  have hsum := linIntAbsParts z
  simp only [GI.Machine.BinOp.eval_add, ← hsum] at dA
  have dC := Det.call (Det.mk2 dA Det.nil) (linBitsEncode_spec hb z.natAbs [])
  simp only [List.nil_append] at dC
  have hflag : (if 0 < (-z).toNat then 1 else 0) = (if z < 0 then 1 else 0) := by
    by_cases hn : z < 0
    · rw [if_pos hn, if_pos (by omega)]
    · rw [if_neg hn, if_neg (by omega)]
  have he : encInt z = .list [.nat (if z < 0 then 1 else 0), linBitsVal z.natAbs.bits] := rfl
  apply FunDet.intro hf
  rw [he]
  have d := Det.mk2 dS dC
  simp only [GI.Machine.BinOp.eval_lt, hflag] at d
  refine d.mono ?_
  have wp : (Val.nat z.toNat).wt < (linIntParts z).wt := wt_le_wt_list (by simp [linIntParts])
  have wn : (Val.nat (-z).toNat).wt < (linIntParts z).wt := wt_le_wt_list (by simp [linIntParts])
  have wm : z.natAbs.bits.length ≤ 2 * (linIntParts z).wt + 1 := by
    rw [← linLenBits, hsum]
    have := len_add_le z.toNat (-z).toNat
    simp only [wt_nat] at wp wn
    omega
  have wM : (Val.nat z.natAbs).wt = z.natAbs.bits.length + 2 := by rw [wt_nat, linLenBits]
  have wB := linBitsVal_wt z.natAbs.bits
  have wI := wt_list2_le (.nat z.natAbs) (.list [])
  have wO := wt_list2_le (.nat (if z < 0 then 1 else 0)) (linBitsVal z.natAbs.bits)
  have wS : (Val.nat (if z < 0 then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have w0 : (Val.nat 0).wt = 2 := rfl
  have wnil : (Val.list []).wt = 4 := rfl
  simp only [GI.Machine.BinOp.eval_add, ← hsum, linIntParts] at *
  unfold linIntCodecCost linBitsEncodeCost
  simp only [List.length_nil, Nat.zero_add]
  nlinarith [Nat.pow_le_pow_left wm 3]

end GI.Lang
