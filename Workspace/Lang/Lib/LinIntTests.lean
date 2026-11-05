module

public import Workspace.Lang.Lib.LinIntDiv

@[expose] public section

namespace GI.Lang
open GI.Cited (Val encInt)

/-- Decode both operands and run the natural-parts comparison core. -/
def linIntCompareF (decode core : ℕ) : Expr :=
  .letE (.call decode (arg 0))
    (.letE (.call decode (arg 1)) (.call core (mk2 (.var 1) (.var 2))))

/-- Signed strict comparison returns one exactly when x < y. -/
theorem linIntCompare_spec {P : Program} {f decode core bd : ℕ}
    (hf : P.funs[f]? = some (linIntCompareF decode core))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (hc : P.funs[core]? = some linIntLtPartsF) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (.nat (if x < y then 1 else 0))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) := by
  have hx := linIntDecode_spec hd hbd x
  have hy := linIntDecode_spec hd hbd y
  have hxy := linIntLtParts_spec hc x y
  have dx := Det.call (Det.arg' (P := P) (vs := [encInt x, encInt y]) (rest := []) (j := 0) rfl) hx
  have dy := Det.call (Det.arg' (P := P) (vs := [encInt x, encInt y])
    (rest := [linIntParts x]) (j := 1) rfl) hy
  have dc := Det.call (Det.mk2
    (Det.var' (P := P) (env := [.list [encInt x, encInt y], linIntParts x, linIntParts y]) (i := 1) rfl)
    (Det.var' (P := P) (env := [.list [encInt x, encInt y], linIntParts x, linIntParts y]) (i := 2) rfl)) hxy
  apply FunDet.intro hf
  refine (Det.letE dx (Det.letE dy dc)).mono ?_
  have wx := wt_le_wt_list (vs := [encInt x, encInt y]) (v := encInt x) (by simp)
  have wy := wt_le_wt_list (vs := [encInt x, encInt y]) (v := encInt y) (by simp)
  have dxB := linIntCodecCost_mono wx.le
  have dyB := linIntCodecCost_mono wy.le
  have wpx := hx.wt_lt
  have wpy := hy.wt_lt
  have wa := wt_list2_le (linIntParts x) (linIntParts y)
  have ha : (Val.list [linIntParts x, linIntParts y]).wt ≤
      4 * linIntCodecCost (Val.list [encInt x, encInt y]).wt + 6 := by omega
  have hC : linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt ≤
      linIntCoreBudget (Val.list [encInt x, encInt y]).wt := linIntPartsCost_mono ha
  have wb : (Val.nat (if x < y then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  unfold linIntBinaryCost
  omega

/-- The three integer constants needed for sign. -/
def linIntZeroE : Expr := mk2 (.nat 0) .nil
def linIntOneE : Expr := mk2 (.nat 0) (mk1 (.nat 1))
def linIntMinusOneE : Expr := mk2 (.nat 1) (mk1 (.nat 1))

/-- Sign is read directly from the sign field and the length of the magnitude bits. -/
def linIntSignF : Expr :=
  .ite (arg 0) linIntMinusOneE (.ite (.length (arg 1)) linIntOneE linIntZeroE)

theorem linIntSign_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some linIntSignF) (z : ℤ) :
    FunDet P f (encInt z) (encInt z.sign) (10000 * ((encInt z).wt + 1) ^ 2) := by
  let s := if z < 0 then 1 else 0
  have hzv : encInt z = .list [.nat s, linBitsVal z.natAbs.bits] := rfl
  have ds := Det.arg' (P := P) (vs := [.nat s, linBitsVal z.natAbs.bits]) (rest := []) (j := 0) rfl
  have dl := Det.length (Det.arg' (P := P) (vs := [.nat s, linBitsVal z.natAbs.bits])
    (rest := []) (j := 1) rfl)
  have d0 := Det.mk2 (Det.nat (P := P) (env := [.list [.nat s, linBitsVal z.natAbs.bits]]) 0) Det.nil
  have d1 := Det.mk2 (Det.nat (P := P) (env := [.list [.nat s, linBitsVal z.natAbs.bits]]) 0)
    (Det.mk1 (Det.nat 1))
  have dn := Det.mk2 (Det.nat (P := P) (env := [.list [.nat s, linBitsVal z.natAbs.bits]]) 1)
    (Det.mk1 (Det.nat 1))
  have d := linDetIte ds dn (linDetIte dl d1 d0)
  have ho : (if s = 0 then
      if (z.natAbs.bits.map fun b => Val.nat (linBit b)).length = 0 then encInt 0 else encInt 1
      else encInt (-1)) = encInt z.sign := by
    cases z with
    | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
        have hp : (n + 1).bits.length ≠ 0 := by
          rw [← linLenBits]
          exact (GI.Machine.len_pos.mpr (by omega)).ne'
        have hs : s = 0 := by dsimp [s]; rw [if_neg (by omega)]
        rw [hs]
        rw [Int.ofNat_eq_natCast, Int.sign_natCast_of_ne_zero (by omega)]
        simp only [Int.natAbs_natCast, List.length_map, if_pos rfl, if_neg hp, ite_true]
    | negSucc n => simp [s, Int.sign]
  change Det P _ linIntSignF (if s = 0 then
    if (z.natAbs.bits.map fun b => Val.nat (linBit b)).length = 0 then encInt 0 else encInt 1
    else encInt (-1)) _ at d
  rw [ho] at d
  apply FunDet.intro hf
  rw [hzv]
  refine d.mono ?_
  have hl : z.natAbs.bits.length < (Val.list [.nat s, linBitsVal z.natAbs.bits]).wt := by
    have h1 := length_lt_wt_list (z.natAbs.bits.map fun b => Val.nat (linBit b))
    have h2 := wt_le_wt_list (vs := [.nat s, linBitsVal z.natAbs.bits])
      (v := linBitsVal z.natAbs.bits) (by simp)
    simp only [List.length_map] at h1
    exact lt_trans h1 h2
  have w0 : (encInt 0).wt ≤ 100 := by decide
  have w1 : (encInt 1).wt ≤ 100 := by decide
  have wn : (encInt (-1)).wt ≤ 100 := by decide
  simp only [List.length_map]
  have c0 : (Val.list [.nat 0, .list []]).wt = (encInt 0).wt := rfl
  have c1 : (Val.list [.nat 0, .list [.nat 1]]).wt = (encInt 1).wt := rfl
  have cn : (Val.list [.nat 1, .list [.nat 1]]).wt = (encInt (-1)).wt := rfl
  have cb : (Val.list [.nat 1]).wt ≤ 100 := by decide
  rw [c0, c1, cn]
  split_ifs <;> nlinarith

end GI.Lang
