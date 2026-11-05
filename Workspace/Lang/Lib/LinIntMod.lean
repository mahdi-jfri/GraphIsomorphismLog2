module

public import Workspace.Lang.Lib.LinIntDiv

@[expose] public section

namespace GI.Lang
open GI.Cited (Val encInt)
open GI.Machine (BinOp)

/-- Remainder on canonical parts. The divisor sign does not change a Euclidean remainder. -/
def linIntModPartsVal (x y : ℤ) : Val :=
  if y.natAbs = 0 then linIntParts x else
    if (-x).toNat = 0 then .list [.nat (x.toNat % y.natAbs), .nat 0]
    else .list [.nat (y.natAbs - 1 - (((-x).toNat - 1) % y.natAbs)), .nat 0]

private theorem linIntNegSuccMod (a b : ℕ) (hb : 0 < b) :
    Int.negSucc a % (b : ℤ) = ((b - 1 - (a % b) : ℕ) : ℤ) := by
  rw [Int.negSucc_emod a (by omega)]
  change (b : ℤ) - 1 - ((a % b : ℕ) : ℤ) = ((b - 1 - (a % b) : ℕ) : ℤ)
  have := Nat.mod_lt a hb
  omega

theorem linIntModPartsVal_eq (x y : ℤ) : linIntModPartsVal x y = linIntParts (x % y) := by
  cases y with
  | ofNat b =>
    by_cases hb : b = 0
    · subst b; simp [linIntModPartsVal]
    · cases x with
      | ofNat a =>
        change linIntModPartsVal (Int.ofNat a) (Int.ofNat b) = linIntParts ((a % b : ℕ) : ℤ)
        have hq : ((a : ℤ) % (b : ℤ)).toNat = a % b := rfl
        have hqp : (0 : ℤ) ≤ (a : ℤ) % (b : ℤ) := Int.emod_nonneg _ (by omega)
        simp [linIntModPartsVal, linIntParts, hb]
        omega
      | negSucc a =>
        change linIntModPartsVal (Int.negSucc a) (b : ℤ) = linIntParts (Int.negSucc a % (b : ℤ))
        rw [linIntNegSuccMod a b (by omega)]
        simp [linIntModPartsVal, linIntParts, hb]
  | negSucc b =>
    have hy : (Int.negSucc b : ℤ) = -((b + 1 : ℕ) : ℤ) := by omega
    conv_rhs => rw [hy, Int.emod_neg]
    cases x with
    | ofNat a =>
      change linIntModPartsVal (Int.ofNat a) (Int.negSucc b) = linIntParts ((a % (b + 1) : ℕ) : ℤ)
      have hq : ((a : ℤ) % ((b + 1 : ℕ) : ℤ)).toNat = a % (b + 1) := rfl
      have hqp : (0 : ℤ) ≤ (a : ℤ) % ((b + 1 : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
      simp [linIntModPartsVal, linIntParts]
      push_cast at hq hqp
      omega
    | negSucc a =>
      rw [linIntNegSuccMod a (b + 1) (by omega)]
      simp [linIntModPartsVal, linIntParts]

def linIntModPosE : Expr := .arith .mod (linPart 0 0) linIntDivAbsE

def linIntModNegE : Expr :=
  .arith .sub (.arith .sub linIntDivAbsE (.nat 1))
    (.arith .mod (.arith .sub (linPart 0 1) (.nat 1)) linIntDivAbsE)

/-- Euclidean remainder. Division by zero returns the original dividend, as in Lean. -/
def linIntModPartsF : Expr :=
  .ite linIntDivAbsE
    (.ite (linPart 0 1) (mk2 linIntModNegE (.nat 0)) (mk2 linIntModPosE (.nat 0)))
    (arg 0)

set_option maxHeartbeats 1000000 in
theorem linIntModParts_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some linIntModPartsF) (x y : ℤ) :
    FunDet P f (.list [linIntParts x, linIntParts y]) (linIntParts (x % y))
      (linIntPartsCost (Val.list [linIntParts x, linIntParts y]).wt) := by
  have xp := linPart_spec (P := P) x y 0 0
  have xn := linPart_spec (P := P) x y 0 1
  have yp := linPart_spec (P := P) x y 1 0
  have yn := linPart_spec (P := P) x y 1 1
  have db := Det.arith (op := .add) yp yn
  have dp := Det.arith (op := .mod) xp db
  have dn := Det.arith (op := .sub) (Det.arith (op := .sub) db (Det.nat 1))
    (Det.arith (op := .mod) (Det.arith (op := .sub) xn (Det.nat 1)) db)
  have d := linDetIte db (linDetIte xn (Det.mk2 dn (Det.nat 0)) (Det.mk2 dp (Det.nat 0)))
    (Det.arg' (P := P) (vs := [linIntParts x, linIntParts y]) (rest := []) (j := 0) rfl)
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11,
    BinOp.eval_add, BinOp.eval_sub, BinOp.eval_mod, ← linIntAbsParts] at d
  change Det P _ linIntModPartsF (linIntModPartsVal x y) _ at d
  rw [linIntModPartsVal_eq] at d
  apply FunDet.intro hf
  refine d.mono ?_
  have wxp := linPartWt x y 0 0
  have wxn := linPartWt x y 0 1
  have wyp := linPartWt x y 1 0
  have wyn := linPartWt x y 1 1
  simp only [linPartNat00, linPartNat01, linPartNat10, linPartNat11] at wxp wxn wyp wyn
  have wb := linArithWt .add y.toNat (-y).toNat
  have wp := linArithWt .mod x.toNat y.natAbs
  have wb1 := linArithWt .sub y.natAbs 1
  have wn1 := linArithWt .sub (-x).toNat 1
  have wnmod := linArithWt .mod ((-x).toNat - 1) y.natAbs
  have wn := linArithWt .sub (y.natAbs - 1) (((-x).toNat - 1) % y.natAbs)
  have wp0 := wt_list2_le (.nat (x.toNat % y.natAbs)) (.nat 0)
  have wn0 := wt_list2_le (.nat (y.natAbs - 1 - (((-x).toNat - 1) % y.natAbs))) (.nat 0)
  have wx := wt_le_wt_list (vs := [linIntParts x, linIntParts y]) (v := linIntParts x) (by simp)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  simp only [BinOp.eval_add, BinOp.eval_sub, BinOp.eval_mod, ← linIntAbsParts] at *
  unfold linIntPartsCost
  split_ifs <;> nlinarith

/-- Public signed remainder on encInt values. -/
theorem linIntMod_spec {P : Program} {f decode core encode bd be : ℕ}
    (hf : P.funs[f]? = some (linIntBinaryF decode core encode))
    (hd : P.funs[decode]? = some (linIntDecodeF bd))
    (hbd : P.funs[bd]? = some (linBitsDecodeF bd))
    (he : P.funs[encode]? = some (linIntEncodeF be))
    (hbe : P.funs[be]? = some (linBitsEncodeF be))
    (hc : P.funs[core]? = some linIntModPartsF) (x y : ℤ) :
    FunDet P f (.list [encInt x, encInt y]) (encInt (x % y))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt) :=
  linIntBinary_spec hf hd hbd he hbe x y (x % y) (linIntModParts_spec hc x y)

end GI.Lang
